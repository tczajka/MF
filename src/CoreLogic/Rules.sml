(*
 * Core logical rules.
 *
 * Define types, terms and theorems.
 *
 * Provides inference rules and axioms.
 *
 * Author: Tomek Czajka, 2017.
 *)

structure Rules :> sig

  type variable_name = string
  type constant_name = string
  type type_variable_name = string
  type type_constant_name = string

  (*
   * Theorem.
   *
   * This is an abstract type.
   *
   * This guarantees that theorems can only be generated from axioms and
   * inference rules.
   *)
  type theorem

  (*
   * A higher order logic type.
   *
   * For example, "a -> bool" is a polymorphic type with a type functor "->"
   * applied to the type variable "a" and the type constant "bool".
   *)
  datatype hol_type =

    (* A type variable, e.g. "a". *)
    TypeVariable of type_variable_name

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
  and type_constructor =
    TypeConstructor of type_constant_name * int (* arity *) * type_definition

  (*
   * Definition of a type or a type constructor.
   *)
  and type_definition =

    (* Undefined, primitive type. *)
    TypeDefinitionPrimitive

  (*
   * Constant.
   *
   * The definition is included here so that we can compare constants.
   * Constants with different definitions compare unequal even if the have the same name and type.
   *)
  and constant =
    Constant of constant_name * hol_type * constant_definition

  (*
   * Definition of a constant.
   *)
  and constant_definition =

    (* Undefined, primitive constant. *)
    ConstantDefinitionPrimitive
  
  (*
   * Untyped term.
   *
   * E.g. "x + y" or "3 < 4".
   *)
  and untyped_term =

    (* A free variable, e.g. "x". *)
    TermFreeVariable of variable_name

    (* A bound variable. 0 is the closest bound variable, 1 next closest, etc. *)
  | TermBoundVariable of int

    (* A constant, e.g. "true" or "+" *)
  | TermConstant of constant

    (* Function application, e.g. "f x". *)
  | TermApplication of term * term

    (* Function abstraction, e.g. "fun x x + 1". *)
  | TermAbstraction of hol_type * term

  (*
   * Term with an assigned type.
   *)
  and term =
    Term of untyped_term * hol_type

end = struct

  type variable_name = string
  type constant_name = string
  type type_variable_name = string
  type type_constant_name = string

  (*
   * A theorem is a list of assumptions and the conclusion.
   *)
  datatype theorem =
    Theorem of term list * term

  and hol_type =
    TypeVariable of type_variable_name
  | TypeApplication of type_constructor * hol_type list

  and type_constructor =
    TypeConstructor of type_constant_name * int (* arity *) * type_definition

  and type_definition =
    TypeDefinitionPrimitive

  and constant =
    Constant of constant_name * hol_type * constant_definition

  and constant_definition =
    ConstantDefinitionPrimitive
  
  and untyped_term =
    TermFreeVariable of variable_name
  | TermBoundVariable of int
  | TermConstant of constant
  | TermApplication of term * term
  | TermAbstraction of hol_type * term

  and term =
    Term of untyped_term * hol_type

end
