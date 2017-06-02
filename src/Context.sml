(*
 * Printing and parsing context.
 *
 * Author: Tomek Czajka, 2017.
 *)

structure Context = struct

  (*
   * Operator associativity.
   *
   * Determines how operators of same precedence associate.
   *)
  datatype operator_associativity =
    (* Associate to the left, e.g. "a + b + c" means "(a + b) + c". *)
    LeftAssociativity
    (* Associate to the right, e.g. "a -> b -> c" means "a -> (b -> c)" *)
  | RightAssociativity
    (* Do not associate to the left or to the right, e.g. "a < b < c" does not mean anything. *)
  | NoAssociativity

  (*
   * Describes how a token is used in a term.
   *)
  datatype token_syntax =
    (* No special rules apply. *)
    RegularToken

    (*
     * Parse as an infix operator.
     *
     * For instance, "2 + 3" means "(+) 2 3" rather than "2 (+) 3".
     *
     * But "(+) 2 3" is also OK. Do not parse as an operator
     * if enclosed in parantheses.
     *)
  | OperatorToken of int (* precedence *) * operator_associativity

    (*
     * Parse as a binder.
     *
     * For instance, if "all" is a binder:
     * "all x x > 3" means "all (fun x x > 3)", and
     *
     * But "(all) (fun x x > 3)" is also OK.
     * Do not parse as a binder if enclosed in parantheses.
     *)
  | BinderToken of int (* precedence *)
end
