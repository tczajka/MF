(**
 * Names of various things: type constructors, constants, variables.
 *
 * @author Tomek Czajka, 2017
 *)

(**
 * Operator associativity.
 *
 * Determines how operators of same precedence associate.
 *)
type operator_associativity =
  | LeftAssociativity
    (** Associate to the left, e.g. "a + b + c" means "(a + b) + c". *)
  | RightAssociativity
    (** Associate to the right, e.g. "a -> b -> c" means "a -> (b -> c)" *)
  | NoAssociativity

(**
 * Operator precedence.
 *
 * Operators with higher precedence is applied first.
 *
 * For instance, if the precedence of "*" is higher than the precedence of "+",
 * "a + b * c" means "a + (b * c)".
 *)
type operator_precedence = int

(**
 * Describes how to parse a given element.
 *)
type token_syntax =
  | RegularSyntax
    (** No special parsing rules apply. *)
  | OperatorSyntax of operator_precedence * operator_associativity
    (**
     * Parse as an infix operator.
     *
     * For instance, "2 + 3" means "(+) 2 3" rather than "2 (+) 3".
     *
     * But "(+) 2 3" is also OK. Do not parse as an operator
     * if enclosed in parantheses.
     *)
  | BinderSyntax
    (**
     * Parse as a binder.
     *
     * For instance, if "all" is a binder:
     * "all x . x > 3" means "all (fun x . x > 3)", and
     * "all x y . x > y" means "all x . all y . x > y".
     *
     * But "(all) (fun x . x > 3)" is also OK.
     * Do not parse as a binder if enclosed in parantheses.
     *)

(**
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

(**
 * Names of things that can appear in terms.
 *)
type name = identifier * token_syntax
