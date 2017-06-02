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
   * Unproven claim.
   *)
  datatype claim = Claim of {
    num_type_vars : int, (* the number of type variables *)
    var_types : hol_type list, (* types of free variables *)
    assumptions : term list,
    conclusion : term
  }

  (*
   * Theorem.
   *
   * This is an abstract type.  This guarantees that theorems can only be
   * generated from axioms and inference rules.
   *)
  type theorem

  val theorem_to_claim : theorem -> claim

  (*
   * Primitive type: boolean ("bool").
   *)
  val boolean : hol_type

  (*
   * Axiom: p |- p
   *)
  val assumption : theorem

  (*
   * Equality and related axioms.
   *)

  (*
   * Primitive constant: equality ("=").
   *)
  val equal : constant

  (*
   * Axiom: equality is reflexive.
   *
   * |- x = x
   *)
  val equal_self : theorem

   (*
    * Axiom: deduce an equivalent statement.
    *
    * If:
    *   A |- p=q
    * and
    *   B |- p
    * then:
    *   A+B |- q
    val deduce_from_equal : theorem * theorem -> theorem
    *)

   (*
    * Rule: deduce iff from two deductions.
    * If:
    *   A,q |- p
    * and:
    *   B,p |- q
    * then:
    *   A+B |- p = q
    val deduce_equal : theorem * theorem -> theorem
    *)

  (*
   * Primitive type constructor: function ("->").
   *)
  val function : type_constant

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
   val apply_function : { num_type_vars : int, var_types : hol_type list, body : term } -> theorem
   *)

   (*
    * Instantiate types and free variables.
    *
    val instantiate :
      theorem * {
        num_type_vars : int,
        var_types : hol_type list,
        type_var_substitutions : hol_type list,
        var_substitutions : term list
      } -> theorem
    *)

   (*
    * Define a constant as equal to a term.
    *
    * val define_constant : { num_type_vars : int, definition : term } -> constant
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
    * val define_arbitrary_constant : theorem -> constant
    *)

   (*
    * |- <some property> c
    * Where "some property" is the "(=) expression" given to define_constant,
    * or the expression given to define_arbitrary_constant.
    *
    * val by_definition : constant -> theorem
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

  datatype hol_type =
    TypeVariable of int
  | TypeApplication of type_constant * hol_type list

  (*
   * A type constant.
   *
   * It may be polymorphic.
   *
   * The definition is included here so that we can compare types.
   *)
  and type_constant = TypeConstant of {
    name : type_name,
    num_type_vars : int,
    definition : type_definition
  }

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
  and constant = Constant of {
    name : string,
    num_type_vars : int,
    the_type : hol_type,
    definition : constant_definition
  }

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

  and claim = Claim of {
    num_type_vars : int,
    var_types : hol_type list,
    assumptions : term list,
    conclusion : term
  }

  and theorem = Theorem of claim

  fun theorem_to_claim (Theorem c) = c

  (*
   * Primitive types.
   *)
  val boolean =
    TypeApplication (
      TypeConstant {
        name = "bool",
        num_type_vars = 0,
        definition = TypeDefinitionPrimitive
      },
      [])

  val function = TypeConstant {
    name = "->",
    num_type_vars = 2,
    definition = TypeDefinitionPrimitive
  }

  (*
   * Primitive constant "=".
   *)
  val equal = Constant {
    name = "=",
    num_type_vars = 1,
    the_type = TypeApplication (function, [TypeVariable 0, TypeVariable 0]),
    definition = ConstantDefinitionPrimitive
  }

  (*
   * Only this module has access to this!
   *)
  val axiom = Theorem

  (*
   * p:bool |- p:bool
   *)
  val assumption : theorem =
    let
      val p = TermVariable 0
    in
      axiom (Claim {
        num_type_vars = 0,
        var_types = [boolean],
        assumptions = [p],
        conclusion = p})
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
      axiom (Claim {
        num_type_vars = 1,
        var_types = [a],
        assumptions = [],
        conclusion = make_equality (a, x, x)})
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
      axiom (Claim {
        num_type_vars = 2,
        var_types = [a, a, make_function_type (a, b)],
        assumptions = [make_equality (a, x, y)],
        conclusion = make_equality (b, TermApplication (f, x), TermApplication (f, y))
      })
    end

end
