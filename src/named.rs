use simplicity::dag::{InternalSharing, PostOrderIterItem};
use simplicity::human_encoding::{ErrorSet, Position};
use simplicity::jet::{Elements, Jet};
use simplicity::node::{
    self, Commit, CommitData, CommitNode, Converter, Inner, NoDisconnect, NoWitness, Node,
};
use simplicity::node::{
    Construct, ConstructData, Constructible, CoreConstructible, JetConstructible,
};
use simplicity::types;
use simplicity::types::arrow::{Arrow, FinalArrow};
use simplicity::{encode, FailEntropy, Value};
use simplicity::{BitWriter, Cmr};

use std::io;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::ProgNode;

pub type NamedCommitNode = Node<Named<Commit<Elements>>>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Named<N> {
    /// Makes the type non-constructible.
    never: std::convert::Infallible,
    /// Required by Rust.
    phantom: std::marker::PhantomData<N>,
}

impl<J: Jet> node::Marker for Named<Commit<J>> {
    type CachedData = NamedCommitData<J>;
    type Witness = NoWitness;
    type Disconnect = <Commit<J> as node::Marker>::Disconnect;
    type SharingId = Arc<str>;
    type Jet = J;

    fn compute_sharing_id(_: Cmr, _cached_data: &Self::CachedData) -> Option<Arc<str>> {
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NamedCommitData<J> {
    /// Data related to the node itself
    internal: Arc<CommitData<J>>,
    /// Name assigned to the node.
    name: Arc<str>,
}

pub trait NamedExt {
    /// Accessor for the node's name
    fn name(&self) -> &Arc<str>;

    /// Accessor for the node's type arrow
    fn arrow(&self) -> &FinalArrow;

    /// Forget the names, yielding an ordinary [`CommitNode`].
    fn to_commit_node(&self) -> Arc<CommitNode<Elements>>;

    /// Encode a Simplicity expression to bits without any witness data
    fn encode<W: io::Write>(&self, w: &mut BitWriter<W>) -> io::Result<usize>;

    /// Encode a Simplicity program to a vector of bytes, without any witness data.
    fn encode_to_vec(&self) -> Vec<u8>;
}

impl NamedExt for NamedCommitNode {
    /// Accessor for the node's name
    fn name(&self) -> &Arc<str> {
        &self.cached_data().name
    }

    /// Accessor for the node's type arrow
    fn arrow(&self) -> &FinalArrow {
        self.cached_data().internal.arrow()
    }

    /// Forget the names, yielding an ordinary [`CommitNode`].
    fn to_commit_node(&self) -> Arc<CommitNode<Elements>> {
        struct Forgetter;

        impl Converter<Named<Commit<Elements>>, Commit<Elements>> for Forgetter {
            type Error = std::convert::Infallible;
            fn convert_witness(
                &mut self,
                _: &PostOrderIterItem<&NamedCommitNode>,
                _: &NoWitness,
            ) -> Result<NoWitness, Self::Error> {
                Ok(NoWitness)
            }

            fn convert_disconnect(
                &mut self,
                _: &PostOrderIterItem<&NamedCommitNode>,
                _: Option<&Arc<CommitNode<Elements>>>,
                _: &NoDisconnect,
            ) -> Result<NoDisconnect, Self::Error> {
                Ok(NoDisconnect)
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&NamedCommitNode>,
                _: node::Inner<&Arc<CommitNode<Elements>>, Elements, &NoDisconnect, &NoWitness>,
            ) -> Result<Arc<CommitData<Elements>>, Self::Error> {
                Ok(Arc::clone(&data.node.cached_data().internal))
            }
        }

        self.convert::<InternalSharing, _, _>(&mut Forgetter)
            .unwrap()
    }

    /// Encode a Simplicity expression to bits without any witness data
    fn encode<W: io::Write>(&self, w: &mut BitWriter<W>) -> io::Result<usize> {
        let program_bits = encode::encode_program(self.to_commit_node().as_ref(), w)?;
        w.flush_all()?;
        Ok(program_bits)
    }

    /// Encode a Simplicity program to a vector of bytes, without any witness data.
    fn encode_to_vec(&self) -> Vec<u8> {
        let mut program_and_witness_bytes = Vec::<u8>::new();
        let mut writer = BitWriter::new(&mut program_and_witness_bytes);
        self.encode(&mut writer)
            .expect("write to vector never fails");
        debug_assert!(!program_and_witness_bytes.is_empty());

        program_and_witness_bytes
    }
}

pub type NamedConstructNode = Node<Named<Construct<Elements>>>;

impl node::Marker for Named<Construct<Elements>> {
    type CachedData = NamedConstructData;
    type Witness = NoWitness;
    type Disconnect = NoDisconnect;
    type SharingId = Arc<str>;
    type Jet = Elements;

    fn compute_sharing_id(_: Cmr, cached_data: &Self::CachedData) -> Option<Arc<str>> {
        Some(Arc::clone(&cached_data.name))
    }
}

pub trait ProgExt: CoreConstructible + Sized {
    fn witness(ident: Arc<str>) -> Self;

    fn h() -> PairBuilder<Self> {
        PairBuilder(Self::iden())
    }

    fn o() -> SelectorBuilder<Self> {
        SelectorBuilder::default().o()
    }

    fn i() -> SelectorBuilder<Self> {
        SelectorBuilder::default().i()
    }

    fn _false() -> Self {
        Self::injl(&Self::unit())
    }

    fn _true() -> Self {
        Self::injr(&Self::unit())
    }

    fn unit_comp(&self) -> Self {
        Self::comp(&Self::unit(), self).unwrap() // composing with unit always typechecks
    }

    fn pair_iden(&self) -> Self {
        Self::pair(self, &Self::iden()).unwrap() // pairing with iden always typechecks
    }

    fn pair_unit(&self) -> Self {
        Self::pair(self, &Self::unit()).unwrap() // pairing with unit always typechecks
    }

    /// `assertl (take s) cmr` always type checks.
    fn assertl_take(&self, cmr: Cmr) -> Self {
        Self::assertl(&Self::take(self), cmr).unwrap()
    }

    /// `assertl (drop s) cmr` always type checks.
    fn assertl_drop(&self, cmr: Cmr) -> Self {
        Self::assertl(&Self::drop_(self), cmr).unwrap()
    }

    /// `assertr cmr (drop s)` always type checks.
    fn assertr_take(cmr: Cmr, right: &Self) -> Self {
        Self::assertr(cmr, &Self::take(right)).unwrap()
    }

    /// `assertr cmr (take s)` always type checks.
    fn assertr_drop(cmr: Cmr, right: &Self) -> Self {
        Self::assertr(cmr, &Self::drop_(right)).unwrap()
    }
}

/// Builder of expressions that contain
/// `take`, `drop` and `iden` only.
///
/// These expressions always type-check.
#[derive(Debug, Clone, Hash)]
pub struct SelectorBuilder<P> {
    selection: Vec<bool>,
    program: PhantomData<P>,
}

impl<P> Default for SelectorBuilder<P> {
    fn default() -> Self {
        Self {
            selection: Vec::default(),
            program: PhantomData,
        }
    }
}

impl<P: ProgExt> SelectorBuilder<P> {
    /// Select the first component '0' of the input pair.
    pub fn o(mut self) -> Self {
        self.selection.push(false);
        self
    }

    /// Select the second component '1' of the input pair.
    pub fn i(mut self) -> Self {
        self.selection.push(true);
        self
    }

    /// Select the current input value.
    pub fn h(self) -> PairBuilder<P> {
        let mut expr = P::iden();
        for bit in self.selection.into_iter().rev() {
            match bit {
                false => expr = P::take(&expr),
                true => expr = P::drop_(&expr),
            }
        }

        PairBuilder(expr)
    }
}

/// Builder of expressions that contain
/// `pair`, `take`, `drop` and `iden` only.
///
/// These expressions always type-check.
#[derive(Debug, Clone, Hash)]
pub struct PairBuilder<P>(P);

impl<P: ProgExt> PairBuilder<P> {
    /// Take the expression.
    pub fn take(self) -> Self {
        Self(P::take(&self.0))
    }

    /// Drop the expression.
    pub fn drop_(self) -> Self {
        Self(P::drop_(&self.0))
    }

    /// Pair two expressions.
    ///
    /// ## Left-associative:
    ///
    /// `a.pair(b).pair(c)` = `pair (pair a b) c`
    ///
    /// `a.pair(b.pair(c))` = `pair a (pair b c)`
    pub fn pair(self, other: Self) -> Self {
        // Expressions that consist of `take`, `drop` and `iden` have a source type
        // that consists of nested products of type variables.
        // Their source type does not contain any units, sums or other concrete types.
        //
        // s : A → B
        // t : A → C
        // ---------
        // pair s t : A → B × C
        //
        // The pair combinator unifies the source type of both subexpressions.
        // Two nested products of type variables can always be unified into
        // a nested product of type variables.
        //
        // Unification errors occur only when products are unified with sums,
        // which is impossible here.
        //
        // By induction, expressions that consist of `pair`, `take`, `drop` and `iden`
        // have a source type that consists of nested products of type variables.
        Self(P::pair(&self.0, &other.0).unwrap())
    }
}

impl<P> PairBuilder<P> {
    /// Build the expression.
    pub fn get(self) -> P {
        self.0
    }
}

impl ProgExt for ProgNode {
    fn witness(ident: Arc<str>) -> Self {
        Arc::new(
            NamedConstructNode::new(
                ident,
                Position::default(),
                Arc::new([]),
                Arc::new([]),
                Inner::Witness(NoWitness),
            )
            .unwrap(),
        )
    }
}

#[derive(Clone, Debug)]
pub struct NamedConstructData {
    /// Data related to the node itself
    internal: ConstructData<Elements>,
    /// Name assigned to the node
    name: Arc<str>,
    /// Position of the node, if it comes from source code.
    position: Position,
    /// User-provided type bounds on the source (will be checked for consistency
    /// but only after the type checking has completed.)
    user_source_types: Arc<[types::Type]>,
    /// User-provided type bounds on the target (will be checked for consistency
    /// but only after the type checking has completed.)
    user_target_types: Arc<[types::Type]>,
}

pub trait ConstructExt: Sized {
    fn _new(
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, NoWitness>,
    ) -> Result<Self, types::Error>;

    /// Construct a named construct node from parts.
    fn new(
        name: Arc<str>,
        position: Position,
        user_source_types: Arc<[types::Type]>,
        user_target_types: Arc<[types::Type]>,
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, NoWitness>,
    ) -> Result<Self, types::Error>;

    /// Creates a copy of a node with a different name.
    fn renamed(&self, new_name: Arc<str>) -> Self;

    /// Accessor for the node's name
    fn name(&self) -> &Arc<str>;

    /// Accessor for the node's position
    fn position(&self) -> Position;

    /// Accessor for the node's arrow
    fn arrow(&self) -> &Arrow;

    /// Finalizes the types of the underlying [`ConstructNode`].
    fn finalize_types_main(&self) -> Result<Arc<NamedCommitNode>, ErrorSet>;

    /// Finalizes the types of the underlying [`ConstructNode`], without setting
    /// the root node's arrow to 1->1.
    fn finalize_types_non_main(&self) -> Result<Arc<NamedCommitNode>, ErrorSet>;

    fn finalize_types_inner(&self, for_main: bool) -> Result<Arc<NamedCommitNode>, ErrorSet>;
}

fn unnamed_data(construct_data: ConstructData<Elements>) -> NamedConstructData {
    NamedConstructData {
        internal: construct_data,
        name: Arc::from("NOT NAMED YET!"),
        position: Position::default(),
        user_source_types: Arc::new([]),
        user_target_types: Arc::new([]),
    }
}

impl CoreConstructible for NamedConstructData {
    fn unit() -> Self {
        unnamed_data(ConstructData::unit())
    }
    fn iden() -> Self {
        unnamed_data(ConstructData::iden())
    }
    fn injl(inner: &Self) -> Self {
        unnamed_data(ConstructData::injl(&inner.internal))
    }
    fn injr(inner: &Self) -> Self {
        unnamed_data(ConstructData::injr(&inner.internal))
    }
    fn take(inner: &Self) -> Self {
        unnamed_data(ConstructData::take(&inner.internal))
    }
    fn drop_(inner: &Self) -> Self {
        unnamed_data(ConstructData::drop_(&inner.internal))
    }
    fn comp(left: &Self, right: &Self) -> Result<Self, types::Error> {
        ConstructData::comp(&left.internal, &right.internal).map(unnamed_data)
    }
    fn case(left: &Self, right: &Self) -> Result<Self, types::Error> {
        ConstructData::case(&left.internal, &right.internal).map(unnamed_data)
    }

    fn assertl(left: &Self, right: Cmr) -> Result<Self, types::Error> {
        ConstructData::assertl(&left.internal, right).map(unnamed_data)
    }
    fn assertr(left: Cmr, right: &Self) -> Result<Self, types::Error> {
        ConstructData::assertr(left, &right.internal).map(unnamed_data)
    }
    fn pair(left: &Self, right: &Self) -> Result<Self, types::Error> {
        ConstructData::pair(&left.internal, &right.internal).map(unnamed_data)
    }

    fn fail(entropy: FailEntropy) -> Self {
        unnamed_data(ConstructData::fail(entropy))
    }
    fn const_word(value: Arc<Value>) -> Self {
        unnamed_data(ConstructData::const_word(value))
    }
}

impl JetConstructible<Elements> for NamedConstructData {
    fn jet(j: Elements) -> Self {
        unnamed_data(ConstructData::jet(j))
    }
}

impl ConstructExt for NamedConstructNode {
    /// Construct a named construct node from parts.
    fn _new(
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, NoWitness>,
    ) -> Result<Self, types::Error> {
        let construct_data = ConstructData::from_inner(
            inner
                .as_ref()
                .map(|data| &data.cached_data().internal)
                .map_disconnect(|_| &None)
                .copy_witness(),
        )?;
        Ok(Node::from_parts(inner, unnamed_data(construct_data)))
    }

    /// Construct a named construct node from parts.
    fn new(
        name: Arc<str>,
        position: Position,
        user_source_types: Arc<[types::Type]>,
        user_target_types: Arc<[types::Type]>,
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, NoWitness>,
    ) -> Result<Self, types::Error> {
        let construct_data = ConstructData::from_inner(
            inner
                .as_ref()
                .map(|data| &data.cached_data().internal)
                .map_disconnect(|_| &None)
                .copy_witness(),
        )?;
        let named_data = NamedConstructData {
            internal: construct_data,
            name,
            position,
            user_source_types,
            user_target_types,
        };
        Ok(Node::from_parts(inner, named_data))
    }

    /// Creates a copy of a node with a different name.
    fn renamed(&self, new_name: Arc<str>) -> Self {
        let data = NamedConstructData {
            internal: self.cached_data().internal.clone(),
            user_source_types: Arc::clone(&self.cached_data().user_source_types),
            user_target_types: Arc::clone(&self.cached_data().user_target_types),
            name: new_name,
            position: self.position(),
        };
        Self::from_parts(self.inner().clone(), data)
    }

    /// Accessor for the node's name
    fn name(&self) -> &Arc<str> {
        &self.cached_data().name
    }

    /// Accessor for the node's position
    fn position(&self) -> Position {
        self.cached_data().position
    }

    /// Accessor for the node's arrow
    fn arrow(&self) -> &Arrow {
        self.cached_data().internal.arrow()
    }

    /// Finalizes the types of the underlying [`ConstructNode`].
    fn finalize_types_main(&self) -> Result<Arc<NamedCommitNode>, ErrorSet> {
        self.finalize_types_inner(true)
    }

    /// Finalizes the types of the underlying [`ConstructNode`], without setting
    /// the root node's arrow to 1->1.
    fn finalize_types_non_main(&self) -> Result<Arc<NamedCommitNode>, ErrorSet> {
        self.finalize_types_inner(false)
    }

    fn finalize_types_inner(&self, for_main: bool) -> Result<Arc<NamedCommitNode>, ErrorSet> {
        struct FinalizeTypes<J: Jet> {
            for_main: bool,
            errors: ErrorSet,
            phantom: PhantomData<J>,
        }

        impl Converter<Named<Construct<Elements>>, Named<Commit<Elements>>> for FinalizeTypes<Elements> {
            type Error = ErrorSet;
            fn convert_witness(
                &mut self,
                _: &PostOrderIterItem<&NamedConstructNode>,
                _: &NoWitness,
            ) -> Result<NoWitness, Self::Error> {
                Ok(NoWitness)
            }

            fn convert_disconnect(
                &mut self,
                _: &PostOrderIterItem<&NamedConstructNode>,
                _: Option<&Arc<NamedCommitNode>>,
                _: &NoDisconnect,
            ) -> Result<NoDisconnect, Self::Error> {
                Ok(NoDisconnect)
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&NamedConstructNode>,
                inner: node::Inner<&Arc<NamedCommitNode>, Elements, &NoDisconnect, &NoWitness>,
            ) -> Result<NamedCommitData<Elements>, Self::Error> {
                let converted_data = inner
                    .as_ref()
                    .map(|node| &node.cached_data().internal)
                    .map_disconnect(|disc| *disc)
                    .copy_witness();

                if !self.for_main {
                    // For non-`main` fragments, treat the ascriptions as normative, and apply them
                    // before finalizing the type.
                    let arrow = data.node.arrow();
                    for ty in data.node.cached_data().user_source_types.as_ref() {
                        if let Err(e) = arrow.source.unify(ty, "binding source type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                    for ty in data.node.cached_data().user_target_types.as_ref() {
                        if let Err(e) = arrow.target.unify(ty, "binding target type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                }

                let commit_data = match CommitData::new(data.node.arrow(), converted_data) {
                    Ok(commit_data) => Arc::new(commit_data),
                    Err(e) => {
                        self.errors.add(data.node.position(), e);
                        return Err(self.errors.clone());
                    }
                };

                if self.for_main {
                    // For `main`, only apply type ascriptions *after* inference has completely
                    // determined the type.
                    let source_bound =
                        types::Bound::Complete(Arc::clone(&commit_data.arrow().source));
                    let source_ty = types::Type::from(source_bound);
                    for ty in data.node.cached_data().user_source_types.as_ref() {
                        if let Err(e) = source_ty.unify(ty, "binding source type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                    let target_bound =
                        types::Bound::Complete(Arc::clone(&commit_data.arrow().target));
                    let target_ty = types::Type::from(target_bound);
                    for ty in data.node.cached_data().user_target_types.as_ref() {
                        if let Err(e) = target_ty.unify(ty, "binding target type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                }

                Ok(NamedCommitData {
                    name: Arc::clone(&data.node.cached_data().name),
                    internal: commit_data,
                })
            }
        }

        let mut finalizer = FinalizeTypes {
            for_main,
            errors: ErrorSet::default(),
            phantom: PhantomData,
        };

        if for_main {
            let unit_ty = types::Type::unit();
            if self.cached_data().user_source_types.is_empty() {
                if let Err(e) = self
                    .arrow()
                    .source
                    .unify(&unit_ty, "setting root source to unit")
                {
                    finalizer.errors.add(self.position(), e);
                }
            }
            if self.cached_data().user_target_types.is_empty() {
                if let Err(e) = self
                    .arrow()
                    .target
                    .unify(&unit_ty, "setting root source to unit")
                {
                    finalizer.errors.add(self.position(), e);
                }
            }
        }

        let root = self.convert::<InternalSharing, _, _>(&mut finalizer)?;
        finalizer.errors.into_result(root)
    }
}
