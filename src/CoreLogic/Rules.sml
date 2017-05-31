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
   * Axiom: p |- p
   *)
  val assumption : theorem

  (*
   * Axiom: equality is reflexive.
   *
   * |- x = x
   *)
  val equal_self : theorem

  (*
   * Axiom: substitute equal arguments.
   *
   * x = y |- f x = f y
   *)
  val argument_substitution : theorem

  (*
   * Axiom: function application to free variable 0 (aka simple beta reduction).
   *
   * |- (fun x body) x = body
   *
   val apply_function : int (* type vars *) * int (* free vars, at least 1 *) * term -> theorem
   *)

   (*
    * Rule: Deduce equivalent statement.
    *
    * If:
    *   A |- p = q
    * and:
    *   B |- p
    * then:
    *   A+B |- q
    val deduce_from_iff : theorem * theorem -> theorem
    *)

   (*
    * Rule: deduce iff from two deductions.
    * If:
    *   A,q |- p
    * and:
    *   B,p |- q
    * then:
    *   A+B |- p = q
    val deduce_iff : theorem * theorem -> theorem
    *)

   (*
    * Instantiate types and free variables.
    *
    val instantiate :
      theorem * int (* new type variables *) * int (* new free variables *)
      * hol_type list * term list -> theorem
    *)

   (*
    * Define a constant as equal to a term.
    *
    * val define_polymorphic_constant : int (* type variables *) * term -> constant
    *)

   (*
   val constant_true : constant
   val constant_false : constant
   val constant_not : constant
   val constant_and : constant
   val constant_or : constant
   val constant_implies : constant
   val constant_all : constant
   val constant_exist : constant
   *)

   (*
    * Define a constant non-constructively.
    *
    * Given: |- (exist) <property>
    * Define a constant with that property.
    *
    * val define_arbitrary_polymorphic_constant : theorem -> constant
    *)

   (*
    * |- <some property> c
    * Where "some property" is the "(=) expression" given to define_constant,
    * or the expression given to define_arbitrary_constant.
    *
    * val constant_definition : constant -> theorem
    *)

  (*
   * Axiom: function extensionality.
   *
   * If values of two function are always same, then the functions are same.
   *
   * all x  f x = g x |- f = g
   *
   val function_extensionality : theorem
   *)

  (*
   * Axiom of choice.
   *
   * all x  exist y  p x y  |-  exist f  all x  p x (f x)
   val axiom_of_choice : theorem
   *)

  (*
   val infinite_type : hol_type

   A polymorphic constant!

   Define is_injective as:  fun f  (fun x fun y  f x = f y) = (=)
   val is_injective : constant

   Define is_surjective as:  fun f  all y  exist x  f x = y
   
   Define is_infinite_type[t] as:
     exist f:t->t  is_injective f and not (is_surjective f)
   val is_infinite_type : constant

   |- is_infinite_type[infinite_type]
   val axiom_of_infinity : theorem
   *)

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
   * p:bool |- p:bool
   *)
  val assumption : theorem =
    let
      val p = TermVariable 0
    in
      Theorem (
        0,   (* no type variables *)
        [boolean],  (* 1 variable of type boolean *)
        [p], (* assumptions *)
        p)  (* conclusion *)
    end

  (*
   * a:t = b:t
   *)
  fun make_equality (t : hol_type, a : term, b : term) : term =
    TermApplication (TermApplication (TermConstant (equal, [t]), a), b)

  (*
   * a -> b
   *)
  fun make_function_type (a : hol_type, b : hol_type) : hol_type =
    TypeApplication (function, [a, b])

  (*
   * |- x:a = x:a
   *)
  val equal_self : theorem =
    let
      val a = TypeVariable 0
      val x = TermVariable 0
    in
      Theorem (
        1,   (* 1 type variable *)
        [a], (* 1 variable of type a *)
        [],  (* No assumptions *)
        make_equality (a, x, x))
    end

  (*
   * For x:a, y:a, f:a->b
   * x = y |- f x = f y
   *)
  val argument_substitution : theorem =
    let
      val a = TypeVariable 0
      val b = TypeVariable 1
      val x = TermVariable 0
      val y = TermVariable 1
      val f = TermVariable 2
    in
      Theorem (
        2,  (* 2 type variables *)
        [a, a, make_function_type (a, b)],  (* three variables x, y, f *)
        [make_equality (a, x, y)],
        make_equality (b, TermApplication (f, x), TermApplication (f, y)))
    end

end
