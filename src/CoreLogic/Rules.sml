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

  type constant_name = string
  type type_name = string

  (*
   * Theorem.
   *
   * This is an abstract type.  This guarantees that theorems can only be
   * generated from axioms and inference rules.
   *)
  type theorem

  (*
   * Type constant (potentially polymorphic).
   *
   * This is an abstract type. This guarantees that type constants can only be
   * defined in a valid way.
   *)
  type type_constant

  (*
   * Constant (potentially polymorphic).
   *
   * This is an abstract type. This guarantees that constants can only be
   * defined in a valid way.
   *)
  type constant

  (*
   * A higher order logic type.
   *
   * For example, "a -> bool" is a polymorphic type with a type functor "->"
   * applied to the type variable "a" and the type "bool".
   *
   * For uniformity, a non-polymorphic type is represented as a polymorphic
   * type with 0 arguments.
   *)
  datatype hol_type =

    (* A type variable. Index into the list of type variables. *)
    TypeVariable of int

    (* A type constant applied to type arguments, e.g. "a -> bool". *)
  | TypeApplication of type_constant * hol_type list

  
  (*
   * Term.
   *
   * E.g. "x + y" or "3 < 4".
   *)
  datatype term =

    (* A variable. 0 is the closest bound variable, 1 next closest, etc. *)
    TermVariable of int

    (*
     * A constant, e.g. "true" or "+".
     *
     * Polymorphic constants are applied to a number of type arguments.
     *)
  | TermConstant of constant * hol_type list

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
  val function : type_constant

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

  type constant_name = string
  type type_name = string

  (*
   * A theorem is a list of assumptions and the conclusion.
   * It may be polymorpic and contain some free variables.
   *)
  datatype theorem =
    Theorem of int (* num type arguments *)
             * hol_type list (* free variables *)
             * term list (* assumptions *)
             * term (* conclusion *)

  and hol_type =
    TypeVariable of int
  | TypeApplication of type_constant * hol_type list

  (*
   * A type constant.
   *
   * It may be polymorphic.
   *
   * The definition is included here so that we can compare types.
   *)
  and type_constant =
    TypeConstant of type_name
                  * int (* num type arguments *)
                  * type_definition

  (*
   * Definition of a type constant
   *)
  and type_definition =
    TypeDefinitionPrimitive (* Undefined, primitive type. *)

  (*
   * Constant.
   *
   * It can be polymorphic.
   *
   * The definition is included here so that we can compare constants.
   *)
  and constant =
    Constant of constant_name
              * int (* num type arguments *)
              * hol_type (* constant type *)
              * constant_definition

  (*
   * Definition of a constant.
   *)
  and constant_definition =
    ConstantDefinitionPrimitive (* Undefined, primitive constant. *)

  and term =
    TermVariable of int
  | TermConstant of constant * hol_type list
  | TermApplication of term * term
  | TermAbstraction of hol_type * term

  (*
   * Primitive types.
   *)
  val boolean : hol_type =
    TypeApplication (TypeConstant ("bool", 0, TypeDefinitionPrimitive), [])

  val function : type_constant =
    TypeConstant ("->", 2, TypeDefinitionPrimitive)

  (*
   * Primitive constant "=".
   *)
  val equal : constant =
    Constant ("=",
              1,
              TypeApplication (function, [TypeVariable 0, TypeVariable 0]),
              ConstantDefinitionPrimitive)

  (*
   * |- x:a = x:a
   *)
  val equal_reflexive : theorem =
    let
      val t = TypeVariable 0
      val x = TermVariable 0
    in
      Theorem (
        1,   (* 1 type variable *)
        [t], (* 1 variable of type t *)
        [],  (* No assumptions *)
        TermApplication (TermApplication (TermConstant (equal, [t]), x), x))
    end

end
