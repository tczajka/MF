(*
 * Types, constants and terms.
 *
 * Author: Tomek Czajka, 2017.
 *)

(* Built-in type. *)
type builtin_type =
  (*
   * Type of booleans, "bool".
   *
   * It is the type of truth claims, true or false.
   *)
  | Bool
  (*
   * Type of functions, "a -> b".
   *
   * It is parametrized by the source type and the destination type.
   *)
  | Function
  (*
   * An infinite type, "infinite_type".
   *
   * This is used so that we can define other infinite types such as natural numbers or real numbers.
   *)
  | InfiniteType

(* Built-in constant. *)
type builtin_constant =
  (*
   * "(=) : a -> a -> bool".
   *
   * Equality.
   *)
  | Equal
  (*
   * "choose : (a -> bool) -> a".
   *
   * Arbitrary choice function
   *
   * Given a predicate that is true for some values, provides any such value.
   * If the predicate is never true, provides any value.
   *)
  | Choose

(*
 * A higher order logic type.
 *
 * For example, "a -> bool" is a polymorphic type with a type functor "->"
 * applied to the type variable "a" and the type constant "bool".
 *
 * The names here are only relevant for pretty-printing and parsing.
 *)
type hol_type =
  (* A type variable, e.g. "a". *)
  | TypeVariable of Names.name
  (* A type constructor application, e.g. "a -> bool". *)
  | TypeApplication of type_constructor * hol_type list

(*
 * Type constructor.
 *
 * "bool" is a type constructor with 0 arguments.
 * "->" is a type constructor with 2 arguments.
 *
 * The definition is included here so that we can compare types.
 * Types with different definitions compare unequal even if they have the same name and arity.
 *)
and type_constructor = TypeConstructor of Names.name * int (* arity *) * type_definition

(* Definition of a type. *)
and type_definition =
  (* Built-in. *)
  | TypeDefinitionBuiltin of builtin_type
  (* Defined via a predicate on some other type. *)
  | TypeDefinitionPredicate of term

(*
 * Constant.
 *
 * The definition is included here so that we can compare constants.
 * Constants with different definitions compare unequal even if the have the same name and type.
 *)
and constant = Constant of name * hol_type * constant_definition

and constant_definition =
  (* Built-in. *)
  | ConstantDefinitionBuiltin of builtin_constant
  (* Defined to be equivalent to a given term. *)
  | ConstantDefinitionTerm of term

(*
 * Term.
 *
 * E.g. "x + y" or "3 < 4".
 *)
and term =
  (* A variable, e.g. "p : bool". *)
  | TermVariable of name * hol_type
  (* A constant, e.g. "true : bool" or "(+) : natural -> natural -> natural" *)
  | TermConstant of constant
  (* Function application, e.g. "f x". *)
  | TermApplication of term * term
  (* Function abstruction, e.g. "fun x . x + 1". *)
  | TermAbstraction of name * term
