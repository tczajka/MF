(*
 * Names of various things: type constructors, constants, variables.
 *
 * Author: Tomek Czajka, 2017.
 *)

(*
 * Operator associativity.
 *
 * Determines how operators of same precedence associate.
 *)
type operator_associativity =
  (* Associate to the left, e.g. "a + b + c" means "(a + b) + c". *)
  | LeftAssociativity
  (* Associate to the right, e.g. "a -> b -> c" means "a -> (b -> c)" *)
  | RightAssociativity
  (* Do not associate to the left or to the right, e.g. "a < b < c" does not mean anything. *)
  | NoAssociativity

(*
 * Operator precedence.
 *
 * Operators with higher precedence are applied first.
 *
 * For instance, if the precedence of "*" is higher than the precedence of "+",
 * "a + b * c" means "a + (b * c)".
 *)
type operator_precedence = int

(*
 * Describes how a token is used in a term.
 *)
type token_syntax =
  (* No special rules apply. *)
  | RegularToken
  (**
   * Parse as an infix operator.
   *
   * For instance, "2 + 3" means "(+) 2 3" rather than "2 (+) 3".
   *
   * But "(+) 2 3" is also OK. Do not parse as an operator
   * if enclosed in parantheses.
   *)
  | OperatorToken of operator_precedence * operator_associativity
  (*
   * Parse as a binder.
   *
   * For instance, if "all" is a binder:
   * "all x . x > 3" means "all (fun x . x > 3)", and
   * "all x y . x > y" means "all x . all y . x > y".
   *
   * But "(all) (fun x . x > 3)" is also OK.
   * Do not parse as a binder if enclosed in parantheses.
   *)
  | BinderToken

(*
 * Identifiers of types, constants, variables.
 *
 * HACK!!!
 *
 * We want an immutable string here, but string is mutable. Nevertheless, use
 * string, because strings will become immutable in a future version of Ocaml.
 * That will likely happen before this project reaches maturity, so just use
 * string for now and never use its mutable features.
 *)
type identifier = string

(*
 * Names of things that can appear in terms.
 *)
type name = Name of identifier * token_syntax
