//! Compile the parsed ast into a simplicity program

use std::str::FromStr;

use simplicity::{jet::Elements, types, Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::error::{Error, RichError, WithSpan};
use crate::num::NonZeroPow2Usize;
use crate::parse::{Pattern, SingleExpressionInner, Span, UIntType};
use crate::{
    named::{ConstructExt, ProgExt},
    parse::{Call, CallName, Expression, ExpressionInner, Program, Statement, Type},
    scope::GlobalScope,
    ProgNode,
};

fn eval_blk(
    stmts: &[Statement],
    scope: &mut GlobalScope,
    index: usize,
    last_expr: Option<&Expression>,
) -> Result<ProgNode, RichError> {
    if index >= stmts.len() {
        return match last_expr {
            Some(expr) => expr.eval(scope, None),
            None => Ok(ProgNode::unit()),
        };
    }
    match &stmts[index] {
        Statement::Assignment(assignment) => {
            let expr = assignment.expression.eval(scope, assignment.ty.as_ref())?;
            scope.insert(assignment.pattern.clone());
            let left = ProgNode::pair(expr, ProgNode::iden()).with_span(assignment.span)?;
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            ProgNode::comp(left, right).with_span(assignment.span)
        }
        Statement::Function(function) => {
            // Don't translate function until its call
            scope.insert_function(function.clone());
            eval_blk(stmts, scope, index + 1, last_expr)
        }
        Statement::Call(call) => {
            let left = call.eval(scope, None)?;
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            let pair = ProgNode::pair(left, right).with_span(call.span)?;
            let drop_iden = ProgNode::drop_(ProgNode::iden());
            ProgNode::comp(pair, drop_iden).with_span(call.span)
        }
    }
}

impl Program {
    pub fn eval(&self, scope: &mut GlobalScope) -> Result<ProgNode, RichError> {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl Call {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        _reqd_ty: Option<&Type>,
    ) -> Result<ProgNode, RichError> {
        let args_expr = self.args.to_expr().eval(scope, None, self.span)?;

        match &self.name {
            CallName::Jet(name) => {
                let jet = Elements::from_str(name.as_inner())
                    .map_err(|_| Error::JetDoesNotExist(name.clone()))
                    .with_span(self.span)?;
                let jet_expr = ProgNode::jet(jet);
                ProgNode::comp(args_expr, jet_expr).with_span(self.span)
            }
            CallName::BuiltIn(..) => unimplemented!("Builtins are not supported yet"),
            CallName::UnwrapLeft => {
                debug_assert!(self.args.as_ref().len() == 1);
                let left_and_unit =
                    ProgNode::pair(args_expr, ProgNode::unit()).with_span(self.span)?;
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertl(take_iden, fail_cmr).with_span(self.span)?;
                ProgNode::comp(left_and_unit, get_inner).with_span(self.span)
            }
            CallName::UnwrapRight | CallName::Unwrap => {
                debug_assert!(self.args.as_ref().len() == 1);
                let right_and_unit =
                    ProgNode::pair(args_expr, ProgNode::unit()).with_span(self.span)?;
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let take_iden = ProgNode::take(ProgNode::iden());
                let get_inner = ProgNode::assertr(fail_cmr, take_iden).with_span(self.span)?;
                ProgNode::comp(right_and_unit, get_inner).with_span(self.span)
            }
            CallName::Function(name) => {
                let function = scope
                    .get_function(name)
                    .ok_or(Error::UndefinedFunction(name.clone()))
                    .with_span(self.span)?;
                let params_pattern = function.params().to_pattern();
                let mut params_scope = scope.to_child(params_pattern);
                let body_expr = function.body().eval(&mut params_scope, None)?;
                ProgNode::comp(args_expr, body_expr).with_span(self.span)
            }
        }
    }
}

impl Expression {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&Type>,
    ) -> Result<ProgNode, RichError> {
        match &self.inner {
            ExpressionInner::BlockExpression(stmts, expr) => {
                scope.push_scope();
                let res = eval_blk(stmts, scope, 0, Some(expr.as_ref()));
                scope.pop_scope();
                res
            }
            ExpressionInner::SingleExpression(e) => e.inner.eval(scope, reqd_ty, self.span),
        }
    }
}

impl SingleExpressionInner {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&Type>,
        span: Span,
    ) -> Result<ProgNode, RichError> {
        let expr = match self {
            SingleExpressionInner::Unit => ProgNode::unit(),
            SingleExpressionInner::Left(l) => {
                let l = l.eval(scope, None)?;
                ProgNode::injl(l)
            }
            SingleExpressionInner::None => ProgNode::injl(ProgNode::unit()),
            SingleExpressionInner::Right(r) | SingleExpressionInner::Some(r) => {
                let r = r.eval(scope, None)?;
                ProgNode::injr(r)
            }
            SingleExpressionInner::False => ProgNode::injl(ProgNode::unit()),
            SingleExpressionInner::True => ProgNode::injr(ProgNode::unit()),
            SingleExpressionInner::Product(l, r) => {
                let l = l.eval(scope, None)?;
                let r = r.eval(scope, None)?;
                ProgNode::pair(l, r).with_span(span)?
            }
            SingleExpressionInner::UnsignedInteger(decimal) => {
                let reqd_ty = reqd_ty.cloned().unwrap_or(Type::UInt(UIntType::U32));
                let ty = reqd_ty
                    .to_uint()
                    .ok_or(Error::TypeValueMismatch(reqd_ty))
                    .with_span(span)?;
                let value = ty.parse_decimal(decimal).with_span(span)?;
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value)).with_span(span)?
            }
            SingleExpressionInner::BitString(bits) => {
                let value = bits.to_simplicity();
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value)).with_span(span)?
            }
            SingleExpressionInner::ByteString(bytes) => {
                let value = bytes.to_simplicity();
                ProgNode::comp(ProgNode::unit(), ProgNode::const_word(value)).with_span(span)?
            }
            SingleExpressionInner::Witness(name) => ProgNode::witness(name.as_inner().clone()),
            SingleExpressionInner::Variable(identifier) => scope
                .get(&Pattern::Identifier(identifier.clone()))
                .map_err(Error::UndefinedVariable)
                .with_span(span)?,
            SingleExpressionInner::Call(call) => call.eval(scope, reqd_ty)?,
            SingleExpressionInner::Expression(expression) => expression.eval(scope, reqd_ty)?,
            SingleExpressionInner::Match {
                scrutinee,
                left,
                right,
            } => {
                let mut l_scope = scope.clone();
                l_scope.insert(
                    left.pattern
                        .get_identifier()
                        .cloned()
                        .map(Pattern::Identifier)
                        .unwrap_or(Pattern::Ignore),
                );
                let l_compiled = left.expression.eval(&mut l_scope, reqd_ty)?;

                let mut r_scope = scope.clone();
                r_scope.insert(
                    right
                        .pattern
                        .get_identifier()
                        .cloned()
                        .map(Pattern::Identifier)
                        .unwrap_or(Pattern::Ignore),
                );
                let r_compiled = right.expression.eval(&mut r_scope, reqd_ty)?;

                // TODO: Enforce target type A + B for m_expr
                let scrutinized_input = scrutinee.eval(scope, None)?;
                let input = ProgNode::pair(scrutinized_input, ProgNode::iden()).with_span(span)?;
                let output = ProgNode::case(l_compiled, r_compiled).with_span(span)?;
                ProgNode::comp(input, output).with_span(span)?
            }
            SingleExpressionInner::Array(elements) => {
                let el_type = if let Some(Type::Array(ty, _)) = reqd_ty {
                    Some(ty.as_ref())
                } else {
                    None
                };
                let nodes = elements
                    .iter()
                    .map(|e| e.eval(scope, el_type))
                    .collect::<Result<Vec<_>, _>>()?;
                let tree = BTreeSlice::from_slice(&nodes);
                tree.fold(ProgNode::pair_unwrap)
            }
            SingleExpressionInner::List(elements) => {
                let el_type = if let Some(Type::List(ty, _)) = reqd_ty {
                    Some(ty.as_ref())
                } else {
                    None
                };
                let nodes = elements
                    .iter()
                    .map(|e| e.eval(scope, el_type))
                    .collect::<Result<Vec<_>, _>>()?;
                let bound = if let Some(Type::List(_, bound)) = reqd_ty {
                    *bound
                } else {
                    NonZeroPow2Usize::next(elements.len().saturating_add(1))
                };

                let partition = Partition::from_slice(&nodes, bound.get() / 2);
                let process = |block: &[ProgNode]| -> ProgNode {
                    if block.is_empty() {
                        ProgNode::injl(ProgNode::unit())
                    } else {
                        let tree = BTreeSlice::from_slice(block);
                        let array = tree.fold(ProgNode::pair_unwrap);
                        ProgNode::injr(array)
                    }
                };

                partition.fold(process, ProgNode::pair_unwrap)
            }
            SingleExpressionInner::ListFold {
                bound,
                list,
                acc,
                ctx,
                name,
            } => {
                let list_expr = list.eval(scope, None)?;
                let acc_expr = acc.eval(scope, None)?;
                let ctx_expr = ctx
                    .as_ref()
                    .map(|e| e.eval(scope, None))
                    .unwrap_or(Ok(ProgNode::unit()))?;
                let args_expr =
                    ProgNode::pair_unwrap(list_expr, ProgNode::pair_unwrap(acc_expr, ctx_expr));

                let function = scope
                    .get_function(name)
                    .ok_or(Error::UndefinedFunction(name.clone()))
                    .with_span(span)?;
                if ctx.is_none() {
                    assert_eq!(
                        function.params().as_ref().len(),
                        2,
                        "List fold expects binary function (element, accumulator) → accumulator"
                    );
                } else {
                    assert_eq!(
                        function.params().as_ref().len(),
                        3,
                        "List fold expects ternary function (element, accumulator, context) → accumulator"
                    );
                }
                let el_var = Pattern::Identifier(function.params().as_ref()[0].clone());
                let acc_var = Pattern::Identifier(function.params().as_ref()[1].clone());
                let ctx_var = function
                    .params()
                    .as_ref()
                    .get(2)
                    .cloned()
                    .map(Pattern::Identifier)
                    .unwrap_or(Pattern::Ignore);
                // list_fold expects a Simplicity expression of type A × (B × C) → B
                // Compile the function body with the corresponding pattern
                // This results in a Simplicity expression with the required type
                let params_pattern = Pattern::product(el_var, Pattern::product(acc_var, ctx_var));
                let mut params_scope = scope.to_child(params_pattern);
                let body_expr = function.body().eval(&mut params_scope, None)?;
                let fold_expr = list_fold(bound.log2(), body_expr).with_span(span)?;

                ProgNode::comp(args_expr, fold_expr).with_span(span)?
            }
            SingleExpressionInner::ForWhile {
                bound,
                acc,
                ctx,
                name,
            } => {
                let acc_expr = acc.eval(scope, None)?;
                let ctx_expr = ctx
                    .as_ref()
                    .map(|e| e.eval(scope, None))
                    .unwrap_or(Ok(ProgNode::unit()))?;
                let args_expr = ProgNode::pair_unwrap(ctx_expr, acc_expr);

                let function = scope
                    .get_function(name)
                    .ok_or(Error::UndefinedFunction(name.clone()))
                    .with_span(span)?;
                if ctx.is_none() {
                    assert_eq!(
                        function.params().as_ref().len(),
                        2,
                        "For-while expects binary function (counter, accumulator) → accumulator"
                    );
                } else {
                    assert_eq!(
                        function.params().as_ref().len(),
                        3,
                        "For-while expects ternary function (counter, accumulator, context) → accumulator"
                    );
                }
                let cnt_var = Pattern::Identifier(function.params().as_ref()[0].clone());
                let acc_var = Pattern::Identifier(function.params().as_ref()[1].clone());
                let ctx_var = function
                    .params()
                    .as_ref()
                    .get(2)
                    .cloned()
                    .map(Pattern::Identifier)
                    .unwrap_or(Pattern::Ignore);
                // for_while expects a Simplicity expression of type (C × 2^(2^(2^n))) × A → B + A
                // Compile the function body with the corresponding pattern
                // This results in a Simplicity expression with the required type
                let params_pattern = Pattern::product(Pattern::product(ctx_var, cnt_var), acc_var);
                let mut params_scope = scope.to_child(params_pattern);
                let body_expr = function.body().eval(&mut params_scope, None)?;
                let for_while_expr = for_while(bound.log2_log2(), body_expr).with_span(span)?;

                ProgNode::comp(args_expr, for_while_expr).with_span(span)?
            }
        };
        if let Some(reqd_ty) = reqd_ty {
            expr.arrow()
                .target
                .unify(&reqd_ty.to_simplicity(), "")
                .map_err(|_| Error::TypeValueMismatch(reqd_ty.clone()))
                .with_span(span)?;
        }
        Ok(expr)
    }
}

// TODO: This function cannot fail if `f` is correctly typed
/// Fold a list of less than `2^n` elements using function `f`.
///
/// The list has type `A^(<2^n)`.
///
/// Function `f: A × (B × C) → B`
/// takes a list element, a state of type `B` and a context of type `C`,
/// and produces an updated state of type `B`.
///
/// The fold `(fold f)_n : A^(<2^n) × (B × C) → B`
/// takes the list, plus an initial state and context,
/// and produces a final (folded) state.
///
/// ## Panics
///
/// n = 0
fn list_fold(n: u32, f: ProgNode) -> Result<ProgNode, types::Error> {
    match n {
        0 => panic!("A^<1 is an illegal type"),
        // (fold f)_1 := case IOH f_0
        1 => {
            let ioh = ProgNode::i().o().h();
            let f_0 = f_array(0, f)?;
            ProgNode::case(ioh, f_0)
        }
        // (fold f)_(n + 1) := OOH ▵ (OIH ▵ IH); case (drop (fold f)_n)) g_n
        // where g_n        := IOH ▵ ((OH ▵ IIH; f_n) ▵ IIIH); (fold f)_n
        m_plus_one => {
            let m = m_plus_one - 1;
            let f_m = f_array(m, f.clone())?;
            let fold_m = list_fold(m, f)?;

            let case_input = ProgNode::pair(
                ProgNode::o().o().h(),
                ProgNode::pair(ProgNode::o().i().h(), ProgNode::i().h())?,
            )?;
            let case_left = ProgNode::drop_(fold_m.clone());
            let f_m_input = ProgNode::pair(ProgNode::o().h(), ProgNode::i().i().h())?;
            let f_m_output = ProgNode::comp(f_m_input, f_m)?;
            let fold_m_input = ProgNode::pair(
                ProgNode::i().o().h(),
                ProgNode::pair(f_m_output, ProgNode::i().i().i().h())?,
            )?;
            let case_right = ProgNode::comp(fold_m_input, fold_m)?;

            ProgNode::comp(case_input, ProgNode::case(case_left, case_right)?)
        }
    }
}

// TODO: This function cannot fail if `f` is correctly typed
/// Generalize a function to work on arrays.
///
/// Function `f : A × (B × C) → B`
/// takes an element of type `A`, a state of type `B` and a context of type `C`,
/// and produces an updated state of type `B`.
///
/// Generalized function `f_n : A^(2^n) × (B × C) → C`
/// takes an array of type `A^(2^n)` plus a state and context,
/// and produces an updated state.
fn f_array(n: u32, f: ProgNode) -> Result<ProgNode, types::Error> {
    match n {
        // f_0 : A × (B × C) → B
        // f_0 := f
        0 => Ok(f),
        // f_(n + 1) : A^(2^(n + 1)) × (B × C) → C
        // f_(n + 1) := OIH ▵ ((OOH ▵ IH; f_n) ▵ IIH); f_n
        m_plus_one => {
            let m = m_plus_one - 1;
            let f_m = f_array(m, f)?;
            let fst_input = ProgNode::pair(ProgNode::o().o().h(), ProgNode::i().h())?;
            let fst_output = ProgNode::comp(fst_input, f_m.clone())?;
            let snd_input = ProgNode::pair(
                ProgNode::o().i().h(),
                ProgNode::pair(fst_output, ProgNode::i().i().h())?,
            )?;
            ProgNode::comp(snd_input, f_m)
        }
    }
}

// TODO: This function cannot fail if `f` is correctly typed
/// Run a function at most `2^(2^n)` times and return the first successful output.
///
/// Function `f: (C × 2^(2^(2^n))) × A → B + A`
/// takes a context of type `C`, a counter of type `2^(2^(2^n))` and a state of type `A`.
/// `f` either returns an output of type `B` or an updated state.
///
/// The loop `forWhile f : C × A → B + A`
/// takes a context and an initial state.
/// The loop runs `f` at most `2^(2^n)` times and returns the first successful output (left value).
/// The loop returns the final state (right value) if `f` never returns an output.
fn for_while(n: u32, f: ProgNode) -> Result<ProgNode, types::Error> {
    match n {
        0 => {
            let fst_input = ProgNode::pair(
                ProgNode::pair(ProgNode::o().h(), ProgNode::_false())?,
                ProgNode::i().h(),
            )?;
            let fst_output = ProgNode::comp(fst_input, f.clone())?;
            let case_input = ProgNode::pair(fst_output, ProgNode::o().h())?;
            let case_left = ProgNode::injl(ProgNode::o().h());
            let snd_input = ProgNode::pair(
                ProgNode::pair(ProgNode::i().h(), ProgNode::_true())?,
                ProgNode::o().h(),
            )?;
            let snd_output = ProgNode::comp(snd_input, f)?;
            let case_output = ProgNode::case(case_left, snd_output)?;
            ProgNode::comp(case_input, case_output)
        }
        m_plus_one => {
            let m = m_plus_one - 1;
            let adapter = ProgNode::pair(
                ProgNode::pair(
                    ProgNode::o().o().o().h(),
                    ProgNode::pair(ProgNode::o().o().i().h(), ProgNode::o().i().h())?,
                )?,
                ProgNode::i().h(),
            )?;
            let adapted_f = ProgNode::comp(adapter, f)?;
            let inner_loop = for_while(m, adapted_f)?;
            for_while(m, inner_loop)
        }
    }
}
