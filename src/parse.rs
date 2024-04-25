//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::collections::HashMap;
use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::elements::hex::FromHex;
use simplicity::types::Type as SimType;
use simplicity::Value;

use crate::array::{BTreeSlice, BinaryTree, Partition};
use crate::error::{Error, RichError, WithSpan};
use crate::num::NonZeroPow2Usize;
use crate::Rule;

/// Area that an object spans inside a file.
///
/// `pest::Span<'i>` forces us to track lifetimes, so we introduce our own struct.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// Line where the object starts.
    ///
    /// Starts at 1.
    pub line: NonZeroUsize,
    /// Column where the object starts.
    ///
    /// Starts at 1.
    pub col: NonZeroUsize,
    /// Length of the object in columns.
    ///
    /// At least 1 column long.
    /// If the object is longer than the line, then the object wraps to the next line.
    pub len: NonZeroUsize,
}

impl Span {
    /// Create a new span with length 1.
    ///
    /// ## Panics
    ///
    /// Line or column are zero.
    pub fn new(line: usize, col: usize) -> Self {
        let line = NonZeroUsize::new(line).expect("PEST lines start at 1");
        let col = NonZeroUsize::new(col).expect("PEST columns start at 1");
        Self {
            line,
            col,
            len: NonZeroUsize::MIN,
        }
    }

    /// Update the length of the span.
    ///
    /// ## Panics
    ///
    /// Length is zero.
    pub fn with_len(self, len: usize) -> Self {
        let len = NonZeroUsize::new(len).expect("PEST tokens are at least 1 character long");
        Self {
            line: self.line,
            col: self.col,
            len,
        }
    }
}

impl<'a> From<&'a pest::iterators::Pair<'_, Rule>> for Span {
    fn from(pair: &'a pest::iterators::Pair<Rule>) -> Self {
        let (line, start) = pair.line_col();
        let span = pair.as_span();
        let len = span.end() - span.start();
        Self::new(line, start).with_len(len)
    }
}

/// A complete simplicity program.
#[derive(Clone, Debug, Hash)]
pub struct Program {
    /// The statements in the program.
    pub statements: Vec<Statement>,
}

/// A statement in a simplicity program.
#[derive(Clone, Debug, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// A function declaration.
    Function(Function),
    /// A function call.
    Call(Call),
}

/// Pattern for binding values to variables.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Pattern {
    /// Bind value to variable name.
    Identifier(Identifier),
    /// Do not bind.
    Ignore,
    /// Split product value. Bind components to first and second pattern, respectively.
    Product(Arc<Self>, Arc<Self>),
    /// Split array value. Bind components to balanced binary tree of patterns.
    Array(Arc<[Self]>),
}

impl Pattern {
    /// Construct a product pattern.
    pub fn product(l: Self, r: Self) -> Self {
        Self::Product(Arc::new(l), Arc::new(r))
    }

    /// Construct an array pattern.
    pub fn array<I: IntoIterator<Item = Self>>(array: I) -> Result<Self, Error> {
        let inner: Arc<_> = array.into_iter().collect();
        if inner.is_empty() {
            Err(Error::ArraySizeZero)
        } else {
            Ok(Self::Array(inner))
        }
    }

    /// Create an equivalent pattern that corresponds to the Simplicity base types.
    ///
    /// ## Base patterns
    ///
    /// - Identifier
    /// - Ignore
    /// - Product
    pub fn to_base(&self) -> Self {
        let binary = BinaryTree::from_tree(self);
        let mut to_base = HashMap::new();

        for data in binary.clone().post_order_iter() {
            match data.node.as_node() {
                Tree::Nullary => {
                    let pattern = (*data.node.as_normal().unwrap()).clone();
                    to_base.insert(data.node, pattern);
                }
                Tree::Binary(l, r) => {
                    let l_converted = to_base.get(&l).unwrap().clone();
                    let r_converted = to_base.get(&r).unwrap().clone();
                    let pattern = Pattern::Product(Arc::new(l_converted), Arc::new(r_converted));
                    to_base.insert(data.node, pattern);
                }
                Tree::Unary(..) => unreachable!("There are no unary patterns"),
                Tree::Nary(..) => unreachable!("Binary trees have no arrays"),
            }
        }

        to_base.remove(&binary).unwrap()
    }
}

impl<'a> TreeLike for &'a Pattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Pattern::Identifier(_) | Pattern::Ignore => Tree::Nullary,
            Pattern::Product(l, r) => Tree::Binary(l, r),
            Pattern::Array(children) => Tree::Nary(children.iter().collect()),
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Pattern::Identifier(i) => write!(f, "{i}")?,
                Pattern::Ignore => write!(f, "_")?,
                Pattern::Product(..) => match data.n_children_yielded {
                    0 => write!(f, "(")?,
                    1 => write!(f, ",")?,
                    n => {
                        debug_assert!(n == 2);
                        write!(f, ")")?;
                    }
                },
                Pattern::Array(children) => match data.n_children_yielded {
                    0 => write!(f, "[")?,
                    n if n == children.len() => write!(f, "]")?,
                    _ => write!(f, ",")?,
                },
            }
        }

        Ok(())
    }
}

/// Identifier of a variable.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Identifier(Arc<str>);

impl Identifier {
    pub fn from_str_unchecked(str: &str) -> Self {
        Self(Arc::from(str))
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The output of an expression is assigned to a pattern.
#[derive(Clone, Debug, Hash)]
pub struct Assignment {
    /// The pattern.
    pub pattern: Pattern,
    /// The return type of the expression.
    pub ty: Option<Type>,
    /// The expression.
    pub expression: Expression,
    /// The source text associated with this assignment.
    pub source_text: Arc<str>,
    /// Area that this assignment spans in the source file.
    pub span: Span,
}

/// A function.
#[derive(Clone, Debug, Hash)]
pub struct Function {
    /// The name of the function
    name: FunctionName,
    /// The parameters of the function.
    ///
    /// Sequence of variables that are used inside the function body.
    params: FunctionParams,
    /// The function body.
    ///
    /// Simfony expression whose variables are function parameters.
    body: Expression,
}

impl Function {
    // Access the function name.
    pub fn name(&self) -> &FunctionName {
        &self.name
    }

    // Access the function parameters.
    pub fn params(&self) -> &FunctionParams {
        &self.params
    }

    // Access the function body.
    pub fn body(&self) -> &Expression {
        &self.body
    }
}

/// A sequence of function parameters.
#[derive(Clone, Debug, Hash)]
pub struct FunctionParams(Arc<[Identifier]>);

impl FunctionParams {
    pub fn to_pattern(&self) -> Pattern {
        match self.0.is_empty() {
            true => Pattern::Ignore,
            false => Pattern::Array(self.0.iter().cloned().map(Pattern::Identifier).collect()),
        }
    }
}

/// A function name.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionName(Arc<str>);

impl FunctionName {
    /// Access the inner name.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for FunctionName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A function call.
#[derive(Clone, Debug, Hash)]
pub struct Call {
    /// The name of the called function.
    pub name: CallName,
    /// The arguments of the call.
    pub args: CallArgs,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// Area that this call spans in the source file.
    pub span: Span,
}

/// A function name.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CallName {
    /// A jet name.
    Jet(JetName),
    /// Left unwrap function
    UnwrapLeft,
    /// Right unwrap function
    UnwrapRight,
    /// Some unwrap function
    Unwrap,
    /// A function name.
    Function(FunctionName),
    /// A builtin function name.
    BuiltIn(Arc<str>),
}

/// String that is a jet name.
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct JetName(Arc<str>);

impl JetName {
    /// Access the inner jet name.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for JetName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// List of arguments for a function call.
#[derive(Clone, Debug, Hash)]
pub struct CallArgs(Arc<[Expression]>);

impl AsRef<[Expression]> for CallArgs {
    fn as_ref(&self) -> &[Expression] {
        self.0.as_ref()
    }
}

impl CallArgs {
    pub fn to_expr(&self) -> SingleExpressionInner {
        match self.0.is_empty() {
            true => SingleExpressionInner::Unit,
            false => SingleExpressionInner::Array(self.0.clone()),
        }
    }
}

/// An expression is something that returns a value.
#[derive(Clone, Debug, Hash)]
pub struct Expression {
    /// The kind of expression
    pub inner: ExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// Area that this expression spans in the source file.
    pub span: Span,
}

/// The kind of expression.
#[derive(Clone, Debug, Hash)]
pub enum ExpressionInner {
    /// A block expression executes a series of statements
    /// and returns the value of the final expression.
    BlockExpression(Vec<Statement>, Arc<Expression>),
    /// A single expression directly returns a value.
    SingleExpression(SingleExpression),
}

/// A single expression directly returns a value.
#[derive(Clone, Debug, Hash)]
pub struct SingleExpression {
    /// The kind of single expression
    pub inner: SingleExpressionInner,
    /// The source text associated with this expression
    pub source_text: Arc<str>,
    /// Area that this expression spans in the source file.
    pub span: Span,
}

/// The kind of single expression.
#[derive(Clone, Debug, Hash)]
pub enum SingleExpressionInner {
    /// Unit literal expression
    Unit,
    /// Left wrapper expression
    Left(Arc<Expression>),
    /// Right wrapper expression
    Right(Arc<Expression>),
    /// Product wrapper expression
    Product(Arc<Expression>, Arc<Expression>),
    /// None literal expression
    None,
    /// Some wrapper expression
    Some(Arc<Expression>),
    /// False literal expression
    False,
    /// True literal expression
    True,
    /// Unsigned integer literal expression
    UnsignedInteger(UnsignedDecimal),
    /// Bit string literal expression
    BitString(Bits),
    /// Byte string literal expression
    ByteString(Bytes),
    /// Witness identifier expression
    Witness(WitnessName),
    /// Variable identifier expression
    Variable(Identifier),
    /// Function call
    Call(Call),
    /// Expression in parentheses
    Expression(Arc<Expression>),
    /// Match expression over a sum type
    Match {
        /// Expression whose output is matched
        scrutinee: Arc<Expression>,
        /// Arm for left sum values
        left: MatchArm,
        /// Arm for right sum values
        right: MatchArm,
    },
    /// Array wrapper expression
    ///
    /// The array must not be empty.
    Array(Arc<[Expression]>),
    /// List wrapper expression
    ///
    /// The exclusive upper bound on the list size is not known at this point
    List(Arc<[Expression]>),
}

/// Valid unsigned decimal string.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct UnsignedDecimal(Arc<str>);

impl UnsignedDecimal {
    /// Access the inner decimal string.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for UnsignedDecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Bit string whose length is a power of two.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Bits {
    /// Least significant bit of byte
    U1(u8),
    /// Two least significant bits of byte
    U2(u8),
    /// Four least significant bits of byte
    U4(u8),
    /// All bits from byte string
    Long(Arc<[u8]>),
}

impl Bits {
    /// Convert the bit string into a Simplicity type.
    pub fn to_simplicity(&self) -> Arc<Value> {
        match self {
            Bits::U1(byte) => Value::u1(*byte),
            Bits::U2(byte) => Value::u2(*byte),
            Bits::U4(byte) => Value::u4(*byte),
            Bits::Long(bytes) => Value::power_of_two(bytes),
        }
    }
}

/// Byte string whose length is a power of two.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Bytes(pub Arc<[u8]>);

impl Bytes {
    /// Convert the byte string into a Simplicity value.
    pub fn to_simplicity(&self) -> Arc<Value> {
        Value::power_of_two(self.0.as_ref())
    }
}

/// String that is a witness name.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct WitnessName(Arc<str>);

impl WitnessName {
    /// Access the inner witness name.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }
}

impl fmt::Display for WitnessName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Arm of a match expression.
#[derive(Clone, Debug, Hash)]
pub struct MatchArm {
    /// Matched pattern
    pub pattern: MatchPattern,
    /// Executed expression
    pub expression: Arc<Expression>,
}

/// Pattern of a match arm.
#[derive(Clone, Debug, Hash)]
pub enum MatchPattern {
    /// Bind inner value of left value to variable name.
    Left(Identifier),
    /// Bind inner value of right value to variable name.
    Right(Identifier),
    /// Match none value (no binding).
    None,
    /// Bind inner value of some value to variable name.
    Some(Identifier),
    /// Match false value (no binding).
    False,
    /// Match true value (no binding).
    True,
}

impl MatchPattern {
    /// Get the variable identifier bound in the pattern.
    pub fn get_identifier(&self) -> Option<&Identifier> {
        match self {
            MatchPattern::Left(i) | MatchPattern::Right(i) | MatchPattern::Some(i) => Some(i),
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }
}

/// A Simphony type.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[non_exhaustive]
pub enum Type {
    Unit,
    Either(Arc<Self>, Arc<Self>),
    Product(Arc<Self>, Arc<Self>),
    Option(Arc<Self>),
    Boolean,
    UInt(UIntType),
    Array(Arc<Self>, NonZeroUsize),
    List(Arc<Self>, NonZeroPow2Usize),
}

/// Normalized unsigned integer type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum UIntType {
    U1,
    U2,
    U4,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256,
}

impl<'a> TreeLike for &'a Type {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Type::Unit | Type::Boolean | Type::UInt(..) => Tree::Nullary,
            Type::Option(l) | Type::Array(l, _) | Type::List(l, _) => Tree::Unary(l),
            Type::Either(l, r) | Type::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

impl Type {
    /// Convert the type into a normalized unsigned integer type.
    /// Return the empty value if the conversion failed.
    pub fn to_uint(&self) -> Option<UIntType> {
        let mut integer_type = HashMap::<&Type, UIntType>::new();
        for data in self.post_order_iter() {
            match data.node {
                Type::Unit => {}
                Type::Either(l, r) => match (l.as_ref(), r.as_ref()) {
                    (Type::Unit, Type::Unit) => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                Type::Product(l, r) => {
                    let uint_l = integer_type.get(l.as_ref())?;
                    let uint_r = integer_type.get(r.as_ref())?;
                    if uint_l != uint_r {
                        return None;
                    }
                    let uint_ty = uint_l.double()?;
                    integer_type.insert(data.node, uint_ty);
                }
                Type::Option(r) => match r.as_ref() {
                    // Option<1> = u1
                    Type::Unit => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
                Type::Boolean => {
                    integer_type.insert(data.node, UIntType::U1);
                }
                Type::UInt(ty) => {
                    integer_type.insert(data.node, *ty);
                }
                Type::Array(el, size) => {
                    if !size.is_power_of_two() {
                        return None;
                    }

                    let mut uint = *integer_type.get(el.as_ref())?;
                    for _ in 0..size.trailing_zeros() {
                        match uint.double() {
                            Some(doubled_uint) => uint = doubled_uint,
                            None => return None,
                        }
                    }
                    integer_type.insert(data.node, uint);
                }
                Type::List(el, bound) => match (el.as_ref(), *bound) {
                    // List<1, 2> = Option<1> = u1
                    (Type::Unit, NonZeroPow2Usize::TWO) => {
                        integer_type.insert(data.node, UIntType::U1);
                    }
                    _ => return None,
                },
            }
        }

        integer_type.remove(self)
    }

    /// Convert the type into a Simplicity type.
    pub fn to_simplicity(&self) -> SimType {
        let mut output = vec![];

        for data in self.post_order_iter() {
            match data.node {
                Type::Unit => output.push(SimType::unit()),
                Type::Either(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::sum(l, r));
                }
                Type::Product(_, _) => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(SimType::product(l, r));
                }
                Type::Option(_) => {
                    let r = output.pop().unwrap();
                    output.push(SimType::sum(SimType::unit(), r));
                }
                Type::Boolean => {
                    output.push(SimType::two_two_n(0));
                }
                Type::UInt(ty) => output.push(ty.to_simplicity()),
                Type::Array(_, size) => {
                    let el = output.pop().unwrap();
                    // Cheap clone because SimType consists of Arcs
                    let el_vector = vec![el; size.get()];
                    let tree = BTreeSlice::from_slice(&el_vector);
                    output.push(tree.fold(SimType::product));
                }
                Type::List(_, bound) => {
                    let el = output.pop().unwrap();
                    // Cheap clone because SimType consists of Arcs
                    let el_vector = vec![el; bound.get() - 1];
                    let partition = Partition::from_slice(&el_vector, bound.get() / 2);
                    debug_assert!(partition.is_complete());
                    let process = |block: &[SimType]| -> SimType {
                        debug_assert!(!block.is_empty());
                        let tree = BTreeSlice::from_slice(block);
                        let array = tree.fold(SimType::product);
                        SimType::sum(SimType::unit(), array)
                    };
                    output.push(partition.fold(process, SimType::product));
                }
            }
        }

        debug_assert!(output.len() == 1);
        output.pop().unwrap()
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Type::Unit => f.write_str("()")?,
                Type::Either(_, _) => match data.n_children_yielded {
                    0 => f.write_str("Either<")?,
                    1 => f.write_str(",")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(">")?;
                    }
                },
                Type::Product(_, _) => match data.n_children_yielded {
                    0 => f.write_str("(")?,
                    1 => f.write_str(", ")?,
                    n => {
                        debug_assert!(n == 2);
                        f.write_str(")")?;
                    }
                },
                Type::Option(_) => match data.n_children_yielded {
                    0 => f.write_str("Option<")?,
                    n => {
                        debug_assert!(n == 1);
                        f.write_str(">")?;
                    }
                },
                Type::Boolean => f.write_str("bool")?,
                Type::UInt(ty) => write!(f, "{ty}")?,
                Type::Array(_, size) => match data.n_children_yielded {
                    0 => f.write_str("[")?,
                    n => {
                        debug_assert!(n == 1);
                        write!(f, "; {size}]")?;
                    }
                },
                Type::List(_, bound) => match data.n_children_yielded {
                    0 => f.write_str("List<")?,
                    n => {
                        debug_assert!(n == 1);
                        write!(f, ", {bound}>")?;
                    }
                },
            }
        }

        Ok(())
    }
}

impl UIntType {
    /// Double the bit width of the type.
    /// Return the empty value upon overflow.
    pub fn double(&self) -> Option<Self> {
        match self {
            UIntType::U1 => Some(UIntType::U2),
            UIntType::U2 => Some(UIntType::U4),
            UIntType::U4 => Some(UIntType::U8),
            UIntType::U8 => Some(UIntType::U16),
            UIntType::U16 => Some(UIntType::U32),
            UIntType::U32 => Some(UIntType::U64),
            UIntType::U64 => Some(UIntType::U128),
            UIntType::U128 => Some(UIntType::U256),
            UIntType::U256 => None,
        }
    }

    /// Parse a decimal string for the type.
    pub fn parse_decimal(&self, decimal: &UnsignedDecimal) -> Result<Arc<Value>, Error> {
        if let UIntType::U128 | UIntType::U256 = self {
            return Err(Error::InvalidDecimal(*self));
        }

        match self {
            UIntType::U1 => decimal.as_inner().parse::<u8>().map(Value::u1),
            UIntType::U2 => decimal.as_inner().parse::<u8>().map(Value::u2),
            UIntType::U4 => decimal.as_inner().parse::<u8>().map(Value::u4),
            UIntType::U8 => decimal.as_inner().parse::<u8>().map(Value::u8),
            UIntType::U16 => decimal.as_inner().parse::<u16>().map(Value::u16),
            UIntType::U32 => decimal.as_inner().parse::<u32>().map(Value::u32),
            UIntType::U64 => decimal.as_inner().parse::<u64>().map(Value::u64),
            _ => unreachable!("Covered by outer match"),
        }
        .map_err(Error::from)
    }

    /// Convert the type into a Simplicity type.
    pub fn to_simplicity(&self) -> SimType {
        match self {
            UIntType::U1 => SimType::two_two_n(0),
            UIntType::U2 => SimType::two_two_n(1),
            UIntType::U4 => SimType::two_two_n(2),
            UIntType::U8 => SimType::two_two_n(3),
            UIntType::U16 => SimType::two_two_n(4),
            UIntType::U32 => SimType::two_two_n(5),
            UIntType::U64 => SimType::two_two_n(6),
            UIntType::U128 => SimType::two_two_n(7),
            UIntType::U256 => SimType::two_two_n(8),
        }
    }
}

impl fmt::Display for UIntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UIntType::U1 => f.write_str("u1"),
            UIntType::U2 => f.write_str("u2"),
            UIntType::U4 => f.write_str("u4"),
            UIntType::U8 => f.write_str("u8"),
            UIntType::U16 => f.write_str("u16"),
            UIntType::U32 => f.write_str("u32"),
            UIntType::U64 => f.write_str("u64"),
            UIntType::U128 => f.write_str("u128"),
            UIntType::U256 => f.write_str("u256"),
        }
    }
}

pub trait PestParse: Sized {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError>;
}

impl PestParse for Program {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::program));
        let mut stmts = Vec::new();
        for inner_pair in pair.into_inner() {
            match inner_pair.as_rule() {
                Rule::statement => stmts.push(Statement::parse(inner_pair)?),
                Rule::EOI => (),
                _ => unreachable!(),
            };
        }
        Ok(Program { statements: stmts })
    }
}

impl PestParse for Statement {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::statement));
        let inner_pair = pair.into_inner().next().unwrap();
        match inner_pair.as_rule() {
            Rule::assignment => Assignment::parse(inner_pair).map(Statement::Assignment),
            Rule::function => Function::parse(inner_pair).map(Statement::Function),
            Rule::call_expr => Call::parse(inner_pair).map(Statement::Call),
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

impl PestParse for Pattern {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::pattern));
        let pair = PatternPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::pattern => {}
                Rule::variable_pattern => {
                    let identifier_pair = data.node.0.into_inner().next().unwrap();
                    let identifier = Identifier::parse(identifier_pair)?;
                    output.push(Pattern::Identifier(identifier));
                }
                Rule::ignore_pattern => {
                    output.push(Pattern::Ignore);
                }
                Rule::product_pattern => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(Pattern::Product(Arc::new(l), Arc::new(r)));
                }
                Rule::array_pattern => {
                    assert!(0 < data.node.n_children(), "Array must be nonempty");
                    let children = output.split_off(output.len() - data.node.n_children());
                    let array = Pattern::array(children).with_span(&data.node.0)?;
                    output.push(array);
                }
                _ => unreachable!("Corrupt grammar"),
            }
        }

        debug_assert!(output.len() == 1);
        Ok(output.pop().unwrap())
    }
}

impl PestParse for Identifier {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::identifier));
        let identifier = Arc::from(pair.as_str());
        Ok(Identifier(identifier))
    }
}

impl PestParse for Assignment {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::assignment));
        let source_text = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let mut inner_pair = pair.into_inner();
        let pattern = Pattern::parse(inner_pair.next().unwrap())?;
        let ty = if let Rule::ty = inner_pair.peek().unwrap().as_rule() {
            Some(Type::parse(inner_pair.next().unwrap())?)
        } else {
            None
        };
        let expression = Expression::parse(inner_pair.next().unwrap())?;
        Ok(Assignment {
            pattern,
            ty,
            expression,
            source_text,
            span,
        })
    }
}

impl PestParse for Function {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::function));
        let mut it = pair.into_inner();
        let name = FunctionName::parse(it.next().unwrap())?;
        let params = FunctionParams::parse(it.next().unwrap())?;
        let body = Expression::parse(it.next().unwrap())?;
        Ok(Self { name, params, body })
    }
}

impl PestParse for FunctionName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::function_name));
        Ok(Self(Arc::from(pair.as_str())))
    }
}

impl PestParse for FunctionParams {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::function_params));
        pair.into_inner()
            .map(Identifier::parse)
            .collect::<Result<Arc<_>, _>>()
            .map(FunctionParams)
    }
}

impl PestParse for Call {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::call_expr));
        let source_text = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let mut inner = pair.into_inner();
        let name = CallName::parse(inner.next().unwrap())?;
        let args = CallArgs::parse(inner.next().unwrap())?;

        Ok(Call {
            name,
            args,
            source_text,
            span,
        })
    }
}

impl PestParse for CallName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::call_name));

        match pair.as_str() {
            "unwrap_left" => Ok(CallName::UnwrapLeft),
            "unwrap_right" => Ok(CallName::UnwrapRight),
            "unwrap" => Ok(CallName::Unwrap),
            _ => {
                let inner = pair.into_inner().next().unwrap();
                match inner.as_rule() {
                    Rule::jet => JetName::parse(inner).map(CallName::Jet),
                    Rule::function_name => FunctionName::parse(inner).map(CallName::Function),
                    _ => panic!("Corrupt grammar"),
                }
            }
        }
    }
}

impl PestParse for JetName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::jet));
        let jet_name = pair.as_str().strip_prefix("jet_").unwrap();
        Ok(Self(Arc::from(jet_name)))
    }
}

impl PestParse for CallArgs {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::call_args));
        pair.into_inner()
            .map(Expression::parse)
            .collect::<Result<Arc<_>, _>>()
            .map(CallArgs)
    }
}

impl PestParse for Expression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        let source_text = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let pair = match pair.as_rule() {
            Rule::expression => pair.into_inner().next().unwrap(),
            Rule::block_expression | Rule::single_expression => pair,
            _ => unreachable!("Corrupt grammar"),
        };

        let inner = match pair.as_rule() {
            Rule::block_expression => {
                let mut stmts = Vec::new();
                let mut inner_pair = pair.into_inner();
                while let Some(Rule::statement) = inner_pair.peek().map(|x| x.as_rule()) {
                    stmts.push(Statement::parse(inner_pair.next().unwrap())?);
                }
                let expr = Expression::parse(inner_pair.next().unwrap())?;
                ExpressionInner::BlockExpression(stmts, Arc::new(expr))
            }
            Rule::single_expression => {
                ExpressionInner::SingleExpression(SingleExpression::parse(pair)?)
            }
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(Expression {
            inner,
            source_text,
            span,
        })
    }
}

impl PestParse for SingleExpression {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::single_expression));

        let source_text: Arc<str> = Arc::from(pair.as_str());
        let span = Span::from(&pair);
        let inner_pair = pair.into_inner().next().unwrap();

        let inner = match inner_pair.as_rule() {
            Rule::unit_expr => SingleExpressionInner::Unit,
            Rule::left_expr => {
                let l = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Left(Arc::new(Expression::parse(l)?))
            }
            Rule::right_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Right(Arc::new(Expression::parse(r)?))
            }
            Rule::product_expr => {
                let mut product_pair = inner_pair.into_inner();
                let l = product_pair.next().unwrap();
                let r = product_pair.next().unwrap();
                SingleExpressionInner::Product(
                    Arc::new(Expression::parse(l)?),
                    Arc::new(Expression::parse(r)?),
                )
            }
            Rule::none_expr => SingleExpressionInner::None,
            Rule::some_expr => {
                let r = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Some(Arc::new(Expression::parse(r)?))
            }
            Rule::false_expr => SingleExpressionInner::False,
            Rule::true_expr => SingleExpressionInner::True,
            Rule::call_expr => SingleExpressionInner::Call(Call::parse(inner_pair)?),
            Rule::bit_string => SingleExpressionInner::BitString(Bits::parse(inner_pair)?),
            Rule::byte_string => SingleExpressionInner::ByteString(Bytes::parse(inner_pair)?),
            Rule::unsigned_integer => {
                SingleExpressionInner::UnsignedInteger(UnsignedDecimal::parse(inner_pair)?)
            }
            Rule::witness_expr => {
                let witness_pair = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Witness(WitnessName::parse(witness_pair)?)
            }
            Rule::variable_expr => {
                let identifier_pair = inner_pair.into_inner().next().unwrap();
                SingleExpressionInner::Variable(Identifier::parse(identifier_pair)?)
            }
            Rule::expression => {
                SingleExpressionInner::Expression(Arc::new(Expression::parse(inner_pair)?))
            }
            Rule::match_expr => {
                let mut it = inner_pair.into_inner();
                let scrutinee_pair = it.next().unwrap();
                let scrutinee = Arc::new(Expression::parse(scrutinee_pair.clone())?);
                let first_arm = MatchArm::parse(it.next().unwrap())?;
                let second_arm = MatchArm::parse(it.next().unwrap())?;

                let (left, right) = match (&first_arm.pattern, &second_arm.pattern) {
                    (MatchPattern::Left(..), MatchPattern::Right(..)) => (first_arm, second_arm),
                    (MatchPattern::Left(..), _) => {
                        return Err(Error::UnmatchedPattern("Right")).with_span(&scrutinee_pair)
                    }
                    (MatchPattern::Right(..), MatchPattern::Left(..)) => (second_arm, first_arm),
                    (MatchPattern::Right(..), _) => {
                        return Err(Error::UnmatchedPattern("Left")).with_span(&scrutinee_pair)
                    }
                    (MatchPattern::None, MatchPattern::Some(..)) => (first_arm, second_arm),
                    (MatchPattern::None, _) => {
                        return Err(Error::UnmatchedPattern("Some")).with_span(&scrutinee_pair)
                    }
                    (MatchPattern::Some(..), MatchPattern::None) => (second_arm, first_arm),
                    (MatchPattern::Some(..), _) => {
                        return Err(Error::UnmatchedPattern("None")).with_span(&scrutinee_pair)
                    }
                    (MatchPattern::False, MatchPattern::True) => (first_arm, second_arm),
                    (MatchPattern::False, _) => {
                        return Err(Error::UnmatchedPattern("true")).with_span(&scrutinee_pair)
                    }
                    (MatchPattern::True, MatchPattern::False) => (second_arm, first_arm),
                    (MatchPattern::True, _) => {
                        return Err(Error::UnmatchedPattern("false")).with_span(&scrutinee_pair)
                    }
                };

                SingleExpressionInner::Match {
                    scrutinee,
                    left,
                    right,
                }
            }
            Rule::array_expr => {
                let elements = inner_pair
                    .clone()
                    .into_inner()
                    .map(|inner| Expression::parse(inner))
                    .collect::<Result<Arc<_>, _>>()?;
                if elements.is_empty() {
                    return Err(Error::ArraySizeZero).with_span(&inner_pair);
                }
                SingleExpressionInner::Array(elements)
            }
            Rule::list_expr => {
                let elements = inner_pair
                    .into_inner()
                    .map(|inner| Expression::parse(inner))
                    .collect::<Result<Arc<_>, _>>()?;
                SingleExpressionInner::List(elements)
            }
            _ => unreachable!("Corrupt grammar"),
        };

        Ok(SingleExpression {
            inner,
            source_text,
            span,
        })
    }
}

impl PestParse for UnsignedDecimal {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::unsigned_integer));
        let decimal = Arc::from(pair.as_str());
        Ok(Self(decimal))
    }
}

impl PestParse for Bits {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::bit_string));
        let bit_string = pair.as_str();
        debug_assert!(&bit_string[0..2] == "0b");

        let bits = &bit_string[2..];
        if !bits.len().is_power_of_two() {
            return Err(Error::BitStringPow2).with_span(&pair);
        }

        let byte_len = (bits.len() + 7) / 8;
        let mut bytes = Vec::with_capacity(byte_len);
        let padding_len = 8usize.saturating_sub(bits.len());
        let padding = std::iter::repeat('0').take(padding_len);
        let mut padded_bits = padding.chain(bits.chars());

        for _ in 0..byte_len {
            let mut byte = 0u8;
            for _ in 0..8 {
                let bit = padded_bits.next().unwrap();
                byte = byte << 1 | if bit == '1' { 1 } else { 0 };
            }
            bytes.push(byte);
        }

        match bits.len() {
            1 => {
                debug_assert!(bytes[0] < 2);
                Ok(Bits::U1(bytes[0]))
            }
            2 => {
                debug_assert!(bytes[0] < 4);
                Ok(Bits::U2(bytes[0]))
            }
            4 => {
                debug_assert!(bytes[0] < 16);
                Ok(Bits::U4(bytes[0]))
            }
            _ => Ok(Bits::Long(bytes.into_iter().collect())),
        }
    }
}

impl PestParse for Bytes {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::byte_string));
        let hex_string = pair.as_str();
        debug_assert!(&hex_string[0..2] == "0x");

        let hex_digits = &hex_string[2..];
        if !hex_digits.len().is_power_of_two() {
            return Err(Error::HexStringPow2).with_span(&pair);
        }

        Vec::<u8>::from_hex(hex_digits)
            .map_err(Error::from)
            .with_span(&pair)
            .map(Arc::from)
            .map(Bytes)
    }
}

impl PestParse for WitnessName {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::witness_name));
        let name = Arc::from(pair.as_str());
        Ok(WitnessName(name))
    }
}

impl PestParse for MatchArm {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::match_arm));
        let mut it = pair.into_inner();
        let pattern = MatchPattern::parse(it.next().unwrap())?;
        let expression = Arc::new(Expression::parse(it.next().unwrap())?);
        Ok(MatchArm {
            pattern,
            expression,
        })
    }
}

impl PestParse for MatchPattern {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::match_pattern));
        let inner_pair = pair.into_inner().next().unwrap();
        let rule = inner_pair.as_rule();
        match rule {
            Rule::left_pattern | Rule::right_pattern | Rule::some_pattern => {
                let identifier_pair = inner_pair.into_inner().next().unwrap();
                let identifier = Identifier::parse(identifier_pair)?;

                match rule {
                    Rule::left_pattern => Ok(MatchPattern::Left(identifier)),
                    Rule::right_pattern => Ok(MatchPattern::Right(identifier)),
                    Rule::some_pattern => Ok(MatchPattern::Some(identifier)),
                    _ => unreachable!("Covered by outer match"),
                }
            }
            Rule::none_pattern => Ok(MatchPattern::None),
            Rule::false_pattern => Ok(MatchPattern::False),
            Rule::true_pattern => Ok(MatchPattern::True),
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

impl PestParse for Type {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        enum Item {
            Type(Type),
            Size(NonZeroUsize),
            Bound(NonZeroPow2Usize),
        }

        impl Item {
            fn unwrap_type(self) -> Type {
                match self {
                    Item::Type(ty) => ty,
                    _ => panic!("Not a type"),
                }
            }

            fn unwrap_size(self) -> NonZeroUsize {
                match self {
                    Item::Size(size) => size,
                    _ => panic!("Not a size"),
                }
            }

            fn unwrap_bound(self) -> NonZeroPow2Usize {
                match self {
                    Item::Bound(size) => size,
                    _ => panic!("Not a bound"),
                }
            }
        }

        assert!(matches!(pair.as_rule(), Rule::ty));
        let pair = TyPair(pair);
        let mut output = vec![];

        for data in pair.post_order_iter() {
            match data.node.0.as_rule() {
                Rule::unit_type => output.push(Item::Type(Type::Unit)),
                Rule::unsigned_type => {
                    let uint_ty = UIntType::parse(data.node.0)?;
                    output.push(Item::Type(Type::UInt(uint_ty)));
                }
                Rule::sum_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    let l = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(Type::Either(Arc::new(l), Arc::new(r))));
                }
                Rule::product_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    let l = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(Type::Product(Arc::new(l), Arc::new(r))));
                }
                Rule::option_type => {
                    let r = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(Type::Option(Arc::new(r))));
                }
                Rule::boolean_type => {
                    output.push(Item::Type(Type::Boolean));
                }
                Rule::array_type => {
                    let size = output.pop().unwrap().unwrap_size();
                    let el = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(Type::Array(Arc::new(el), size)));
                }
                Rule::array_size => {
                    let size_str = data.node.0.as_str();
                    let size = size_str
                        .parse::<NonZeroUsize>()
                        .map_err(|_| Error::ArraySizeZero)
                        .with_span(&data.node.0)?;
                    output.push(Item::Size(size));
                }
                Rule::list_type => {
                    let bound = output.pop().unwrap().unwrap_bound();
                    let el = output.pop().unwrap().unwrap_type();
                    output.push(Item::Type(Type::List(Arc::new(el), bound)));
                }
                Rule::list_bound => {
                    let bound_str = data.node.0.as_str();
                    let bound = bound_str
                        .parse::<NonZeroPow2Usize>()
                        .map_err(|_| Error::ListBoundPow2)
                        .with_span(&data.node.0)?;
                    output.push(Item::Bound(bound));
                }
                Rule::ty => {}
                _ => unreachable!("Corrupt grammar"),
            }
        }

        debug_assert!(output.len() == 1);
        Ok(output.pop().unwrap().unwrap_type())
    }
}

impl PestParse for UIntType {
    fn parse(pair: pest::iterators::Pair<Rule>) -> Result<Self, RichError> {
        assert!(matches!(pair.as_rule(), Rule::unsigned_type));
        let ty = match pair.as_str() {
            "u1" => UIntType::U1,
            "u2" => UIntType::U2,
            "u4" => UIntType::U4,
            "u8" => UIntType::U8,
            "u16" => UIntType::U16,
            "u32" => UIntType::U32,
            "u64" => UIntType::U64,
            "u128" => UIntType::U128,
            "u256" => UIntType::U256,
            _ => unreachable!("Corrupt grammar"),
        };
        Ok(ty)
    }
}

/// Pair of tokens from the 'pattern' rule.
#[derive(Clone, Debug)]
struct PatternPair<'a>(pest::iterators::Pair<'a, Rule>);

impl<'a> TreeLike for PatternPair<'a> {
    fn as_node(&self) -> Tree<Self> {
        let mut it = self.0.clone().into_inner();
        match self.0.as_rule() {
            Rule::variable_pattern | Rule::ignore_pattern => Tree::Nullary,
            Rule::pattern => {
                let l = it.next().unwrap();
                Tree::Unary(PatternPair(l))
            }
            Rule::product_pattern => {
                let l = it.next().unwrap();
                let r = it.next().unwrap();
                Tree::Binary(PatternPair(l), PatternPair(r))
            }
            Rule::array_pattern => {
                let children: Arc<[PatternPair]> = it.map(PatternPair).collect();
                Tree::Nary(children)
            }
            _ => unreachable!("Corrupt grammar"),
        }
    }
}

/// Pair of tokens from the 'ty' rule.
#[derive(Clone, Debug)]
struct TyPair<'a>(pest::iterators::Pair<'a, Rule>);

impl<'a> TreeLike for TyPair<'a> {
    fn as_node(&self) -> Tree<Self> {
        let mut it = self.0.clone().into_inner();
        match self.0.as_rule() {
            Rule::unit_type
            | Rule::boolean_type
            | Rule::unsigned_type
            | Rule::array_size
            | Rule::list_bound => Tree::Nullary,
            Rule::ty | Rule::option_type => {
                let l = it.next().unwrap();
                Tree::Unary(TyPair(l))
            }
            Rule::sum_type | Rule::product_type | Rule::array_type | Rule::list_type => {
                let l = it.next().unwrap();
                let r = it.next().unwrap();
                Tree::Binary(TyPair(l), TyPair(r))
            }
            _ => unreachable!("Corrupt grammar"),
        }
    }
}
