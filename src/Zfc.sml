(*
 * First-order logic and ZFC axioms.
 *
 * Author: Tomek Czajka, 2018.
 *)

structure Zfc :>
sig

  datatype term_type =
    Bool
  | Set
  | Operation of term_type * term_type

  type variable = string * term_type

  type defined_constant

  datatype constant =
    False
  | Implies
  | In
  | TheOnly
  | Defined of defined_constant

  datatype term =
    Constant of constant
  | BoundVariable of int
  | UnboundVariable of variable
  | Application of term * term
  | Lambda of variable * term

  datatype claim =
    Claim of term list * term

  type theorem

end =
struct

  datatype term_type =
    Bool
  | Set
  | Operation of term_type * term_type

  type variable = string * term_type

  (*
   * This is abstract so that we don't have to
   * type-check every time
   *)
  datatype defined_constant =
    DefinedConstant of string * term_type * term

  and constant =
    False
  | Implies
  | In
  | TheOnly
  | Defined of defined_constant

  and term =
    Constant of constant
  | BoundVariable of int
  | UnboundVariable of variable
  | Application of term * term
  | Lambda of variable * term

  datatype claim =
    Claim of term list * term

  datatype theorem = Theorem of claim

end
