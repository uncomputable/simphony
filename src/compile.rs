//! Compile the parsed ast into a simplicity program

use std::str::FromStr;

use simplicity::node::{CoreConstructible as _, JetConstructible as _};
use simplicity::{jet::Elements, Cmr, FailEntropy};

use crate::array::{BTreeSlice, Partition};
use crate::num::NonZeroPow2Usize;
use crate::parse::{Pattern, SingleExpressionInner, Span};
use crate::scope::BasePattern;
use crate::{
    error::{Error, RichError, WithSpan},
    named::{ConstructExt, ProgExt},
    parse::{Expression, ExpressionInner, FuncCall, FuncType, Program, Statement},
    scope::GlobalScope,
    types::{ResolvedType, StructuralType, TypeInner, UIntType},
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
            let ty = scope
                .resolve(&assignment.ty)
                .map_err(Error::UndefinedAlias)
                .with_span(assignment.span)?;
            let expr = assignment.expression.eval(scope, Some(&ty))?;
            scope.insert(assignment.pattern.clone());
            let left = ProgNode::pair_iden(&expr);
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            ProgNode::comp(&left, &right).with_span(assignment.span)
        }
        Statement::FuncCall(func_call) => {
            let left = func_call.eval(scope, None)?;
            let right = eval_blk(stmts, scope, index + 1, last_expr)?;
            combine_seq(&left, &right).with_span(func_call.span)
        }
        Statement::TypeAlias(alias) => {
            scope
                .insert_alias(alias.name.clone(), alias.ty.clone())
                .map_err(Error::UndefinedAlias)
                .with_span(alias.span)?;
            eval_blk(stmts, scope, index + 1, last_expr)
        }
    }
}

fn combine_seq(a: &ProgNode, b: &ProgNode) -> Result<ProgNode, simplicity::types::Error> {
    let pair = ProgNode::pair(a, b)?;
    let drop_iden = ProgNode::drop_(&ProgNode::iden());
    ProgNode::comp(&pair, &drop_iden)
}

impl Program {
    pub fn eval(&self, scope: &mut GlobalScope) -> Result<ProgNode, RichError> {
        eval_blk(&self.statements, scope, 0, None)
    }
}

impl FuncCall {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        _reqd_ty: Option<&ResolvedType>,
    ) -> Result<ProgNode, RichError> {
        match &self.func_type {
            FuncType::Jet(name) => {
                let args = match self.args.is_empty() {
                    true => SingleExpressionInner::Unit,
                    false => SingleExpressionInner::Array(self.args.clone()),
                };
                // TODO: Pass the jet source type here.
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let args_expr = args.eval(scope, None, self.span)?;
                let jet = Elements::from_str(name.as_inner())
                    .map_err(|_| Error::JetDoesNotExist(name.as_inner().clone()))
                    .with_span(self.span)?;
                let jet_expr = ProgNode::jet(jet);
                ProgNode::comp(&args_expr, &jet_expr).with_span(self.span)
            }
            FuncType::BuiltIn(..) => unimplemented!("Builtins are not supported yet"),
            FuncType::UnwrapLeft => {
                debug_assert!(self.args.len() == 1);
                let b = self.args[0].eval(scope, None)?;
                let left_and_unit = ProgNode::pair_unit(&b);
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertl_take(&ProgNode::iden(), fail_cmr);
                ProgNode::comp(&left_and_unit, &get_inner).with_span(self.span)
            }
            FuncType::UnwrapRight | FuncType::Unwrap => {
                debug_assert!(self.args.len() == 1);
                let c = self.args[0].eval(scope, None)?;
                let right_and_unit = ProgNode::pair_unit(&c);
                let fail_cmr = Cmr::fail(FailEntropy::ZERO);
                let get_inner = ProgNode::assertr_take(fail_cmr, &ProgNode::iden());
                ProgNode::comp(&right_and_unit, &get_inner).with_span(self.span)
            }
        }
    }
}

impl Expression {
    pub fn eval(
        &self,
        scope: &mut GlobalScope,
        reqd_ty: Option<&ResolvedType>,
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
        reqd_ty: Option<&ResolvedType>,
        span: Span,
    ) -> Result<ProgNode, RichError> {
        let expr = match self {
            SingleExpressionInner::Unit => ProgNode::unit(),
            SingleExpressionInner::Left(l) => {
                let l = l.eval(scope, None)?;
                ProgNode::injl(&l)
            }
            SingleExpressionInner::None => ProgNode::_false(),
            SingleExpressionInner::Right(r) | SingleExpressionInner::Some(r) => {
                let r = r.eval(scope, None)?;
                ProgNode::injr(&r)
            }
            SingleExpressionInner::False => ProgNode::_false(),
            SingleExpressionInner::True => ProgNode::_true(),
            SingleExpressionInner::Product(l, r) => {
                let l = l.eval(scope, None)?;
                let r = r.eval(scope, None)?;
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                ProgNode::pair(&l, &r).with_span(span)?
            }
            SingleExpressionInner::UnsignedInteger(decimal) => {
                let reqd_ty = reqd_ty
                    .cloned()
                    .unwrap_or(ResolvedType::from(UIntType::U32));
                let ty = UIntType::try_from(&reqd_ty)
                    .map_err(|_| Error::TypeValueMismatch(reqd_ty))
                    .with_span(span)?;
                let value = ty.parse_decimal(decimal).with_span(span)?;
                ProgNode::unit_comp(&ProgNode::const_word(value))
            }
            SingleExpressionInner::BitString(bits) => {
                let value = bits.to_simplicity();
                ProgNode::unit_comp(&ProgNode::const_word(value))
            }
            SingleExpressionInner::ByteString(bytes) => {
                let value = bytes.to_simplicity();
                ProgNode::unit_comp(&ProgNode::const_word(value))
            }
            SingleExpressionInner::Witness(name) => ProgNode::witness(name.as_inner().clone()),
            SingleExpressionInner::Variable(identifier) => scope
                .get(&BasePattern::Identifier(identifier.clone()))
                .ok_or(Error::UndefinedVariable(identifier.clone()))
                .with_span(span)?,
            SingleExpressionInner::FuncCall(call) => call.eval(scope, reqd_ty)?,
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
                let input = ProgNode::pair_iden(&scrutinized_input);
                let output = ProgNode::case(&l_compiled, &r_compiled).with_span(span)?;
                ProgNode::comp(&input, &output).with_span(span)?
            }
            SingleExpressionInner::Array(elements) => {
                let el_type = match reqd_ty.map(ResolvedType::as_inner) {
                    Some(TypeInner::Array(el_type, size)) => {
                        if size.get() != elements.len() {
                            return Err(Error::TypeValueMismatch(reqd_ty.unwrap().clone()))
                                .with_span(span);
                        }
                        Some(el_type.as_ref())
                    }
                    _ => None,
                };
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let nodes: Vec<Result<ProgNode, RichError>> =
                    elements.iter().map(|e| e.eval(scope, el_type)).collect();
                let tree = BTreeSlice::from_slice(&nodes);
                tree.fold(|res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span)))
                })?
            }
            SingleExpressionInner::List(elements) => {
                let el_type = match reqd_ty.map(ResolvedType::as_inner) {
                    Some(TypeInner::List(el_type, _)) => Some(el_type.as_ref()),
                    _ => None,
                };
                let nodes: Vec<Result<ProgNode, RichError>> =
                    elements.iter().map(|e| e.eval(scope, el_type)).collect();
                let bound = match reqd_ty.map(ResolvedType::as_inner) {
                    Some(TypeInner::List(_, bound)) => *bound,
                    _ => NonZeroPow2Usize::next(elements.len().saturating_add(1)),
                };
                if bound.get() <= nodes.len() {
                    return Err(Error::TypeValueMismatch(reqd_ty.unwrap().clone())).with_span(span);
                }
                // FIXME: Constructing pairs should never fail because when Simfony is translated to
                // Simplicity the input type is variable. However, the fact that pairs always unify
                // is hard to prove at the moment, while Simfony lacks a type system.
                let partition = Partition::from_slice(&nodes, bound.get() / 2);
                let process =
                    |block: &[Result<ProgNode, RichError>]| -> Result<ProgNode, RichError> {
                        if block.is_empty() {
                            Ok(ProgNode::_false())
                        } else {
                            let tree = BTreeSlice::from_slice(block);
                            let array = tree.fold(|res_a, res_b| {
                                res_a.and_then(|a| {
                                    res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span))
                                })
                            })?;
                            Ok(ProgNode::injr(&array))
                        }
                    };

                partition.fold(process, |res_a, res_b| {
                    res_a.and_then(|a| res_b.and_then(|b| ProgNode::pair(&a, &b).with_span(span)))
                })?
            }
        };
        if let Some(reqd_ty) = reqd_ty {
            expr.arrow()
                .target
                .unify(&StructuralType::from(reqd_ty).to_unfinalized(), "")
                .map_err(|_| Error::TypeValueMismatch(reqd_ty.clone()))
                .with_span(span)?;
        }
        Ok(expr)
    }
}
