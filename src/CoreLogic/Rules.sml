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
   * Term.
   *
   * E.g. "x + y" or "3 < 4".
   *)
  and term =

    (* A free variable, e.g. "x". *)
    TermFreeVariable of variable_name * hol_type

    (* A bound variable. 0 is the closest bound variable, 1 next closest, etc. *)
  | TermBoundVariable of int

    (* A constant, e.g. "true" or "+".
     *
     * Contains a type because constants can be specialized.
     *)
  | TermConstant of constant * hol_type

    (* Function application, e.g. "f x". *)
  | TermApplication of term * term

    (* Function abstraction, e.g. "fun x x + 1". *)
  | TermAbstraction of hol_type * term

  (*
   * Primitive type: boolean ("bool").
   *)
  val boolean : hol_type

  (*
   * Primitive type constructor: function ("->").
   *)
  val function : type_constructor

  (*
   * Primitive constant: equality ("=").
   *)
  val equal : constant

  (*
   * Axiom: equality is reflexive.
   *
   * |- x:a = x:a
   *)
  val equal_reflexive : theorem

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
  
  and term =
    TermFreeVariable of variable_name * hol_type
  | TermBoundVariable of int
  | TermConstant of constant * hol_type
  | TermApplication of term * term
  | TermAbstraction of hol_type * term

  (*
   * Primitive types.
   *)
  val boolean_constructor : type_constructor =
    TypeConstructor ("bool", 0, TypeDefinitionPrimitive)

  val boolean : hol_type =
    TypeApplication (boolean_constructor, [])

  val function : type_constructor =
    TypeConstructor ("->", 2, TypeDefinitionPrimitive)

  fun make_function_type (a : hol_type, b : hol_type) : hol_type =
    TypeApplication (function, [a, b])

  (*
   * Primitive constant "=".
   *)
  val equal : constant =
    Constant ("=",
              TypeApplication (function, [TypeVariable "a", TypeVariable "a"]),
              ConstantDefinitionPrimitive)

  (*
   * A list of bound variable types.
   *
   * First element is the closest binding.
   *)
  type bound_variables = hol_type list

  (*
   * Type of a term in a bound variable context.
   *
   * Assumes the term is well-formed.
   *
   * FIXME: This should probably not assume that.
   *)
  fun type_of_subterm (bound : bound_variables) : term -> hol_type = fn
    TermFreeVariable (_, typ) => typ
  | TermBoundVariable i => List.nth (bound, i)
  | TermConstant (_, typ) => typ
  | TermApplication (f, _) => (
      case type_of_subterm bound f of
        TypeApplication (type_constructor, [_, return_type]) =>
          if type_constructor = function then
            return_type
          else
            raise Fail "Non-function in function application"
      | _ => raise Fail "Non-function in function application")
  | TermAbstraction (variable_type, t) =>
      make_function_type (variable_type, type_of_subterm (variable_type :: bound) t)

  val type_of_term = type_of_subterm []

  (*
   * "x = y"
   *
   * Assumes x and y are well formed and have the same type.
   *
   * FIXME: This should probably not assume that.
   *)
  fun make_equality (x:term, y:term) : term =
    let
      val t = type_of_term x
      val eq_t = make_function_type (t, make_function_type (t, boolean))
    in
      TermApplication (TermApplication (TermConstant (equal, eq_t), x), y)
    end

  (*
   * |- x:a = x:a
   *)
  val equal_reflexive : theorem =
    let
      val x = TermFreeVariable ("x", TypeVariable "a")
    in
      Theorem ([], make_equality (x, x))
    end

end
