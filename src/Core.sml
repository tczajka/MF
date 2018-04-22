(*
 * First-order logic and ZFC axioms.
 *
 * Author: Tomek Czajka, 2018.
 *)

structure Core :>
sig

  datatype mf_type =
    Bool
  | Set
  | Operation of mf_type * mf_type

  type variable = string * mf_type

  type constant

  datatype term =
    Constant of constant
  | BoundVariable of int
  | UnboundVariable of variable
  | Application of term * term
  | Lambda of variable * term

  val type_of_constant : constant -> mf_type

  (*
   * Given bound variable types and a term, return the type.
   *)
  val type_of_term : term * mf_type list -> mf_type

  type theorem

end =

struct

  datatype mf_type =
    Bool
  | Set
  | Operation of mf_type * mf_type

  type variable = string * mf_type

  (*
   * This is abstract so that we don't have to
   * type-check every time.
   *)
  datatype constant =
    False
  | Implies
  | All
  | In
  | TheOnly
  | Defined of string * mf_type * term

  and term =
    Constant of constant
  | BoundVariable of int
  | UnboundVariable of variable
  | Application of term * term
  | Lambda of variable * term

  fun type_of_constant (c : constant) =
    case c of
      False => Bool
    | Implies => Operation (Bool, Operation (Bool, Bool))
    | All => Operation (Operation (Set, Bool), Bool)
    | In => Operation (Set, Operation (Set, Bool))
    | TheOnly => Operation (Operation (Set, Bool),  Set)
    | Defined (_, t, _) => t

  fun type_of_term (a : term, bound_var_types : mf_type list) =
    case a of
      Constant c => type_of_constant c
    | BoundVariable i => List.nth (bound_var_types, i)
    | UnboundVariable (_, t) => t
    | Application (b, c) =>
        (case type_of_term (b, bound_var_types) of
          Operation (t1, t2) =>
            if type_of_term (c, bound_var_types) = t2
            then t2
            else raise Fail "Type mismatch in application"
         | _ => raise Fail "Not an operation")
    | Lambda ((_, t), b) =>
        Operation (t, type_of_term (b, t :: bound_var_types))

  datatype theorem = Theorem of term list * term

end
