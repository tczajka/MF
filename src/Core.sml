(*
 * First-order logic and ZFC axioms.
 *
 * Author: Tomek Czajka, 2018.
 *)

structure Core :>
sig

  (*
   * Base type, e.g. bool, set, or a defined type.
   *
   * This is abstract so that malformed types cannot be created.
   *)
  type base_type

  (*
   * Term types, e.g. bool, set, set -> bool.
   *)
  datatype mf_type =
    BaseType of base_type
  | Operation of mf_type * mf_type

  (*
   * A constant.
   *
   * This is abstract so that mal-typed constants cannot be created.
   *)
  type constant

  (*
   * Term, e.g. "all x . x in x".
   *)
  datatype term =
    Constant of constant
  | BoundVariable of int
  | FreeVariable of string
  | Application of term * term
  | Lambda of string * mf_type * term

  (*
   * A proved theorem.
   *)
  type theorem

  (*
   * The boolean type.
   *)
  val bool_t : mf_type

  (*
   * The set type.
   *)
  val set : mf_type

  (*
   * Define a new type.
   *
   * The definition must be of type (set -> bool).
   *
   * This defines a criterion for sets (i.e. a class of sets) that belong to
   * the new type.
   *)
  val define_type : string * term -> mf_type

  (*
   * Define a new constant.
   *)
  val define : string * term -> term

  (*
   * false : bool
   *
   * Built-in.
   *)
  val false_c : term

  (*
   * => : bool -> bool -> bool
   *
   * Built-in implication operator.
   *)
  val implies : term

  (*
   * not : bool -> bool
   *
   * Defined as: not p = p => false.
   *)
  val not_c : term

  (*
   * or : bool -> bool -> bool
   *
   * Defined as: p or q = not p => q
   *)
  val or_c : term

  (*
   * and : bool -> bool -> bool
   *
   * Defined as: p and q = not (not p or not q)
   *)
  val and_c : term

  (*
   * <=> : bool -> bool -> bool
   *
   * Defined as: p <=> q = (p => q) and (q => p).
   *)
  val iff : term

  (*
   * = : set -> set -> bool
   *
   * Built-in set equality operator.
   *)
  val equal : term

  (*
   * all : (set -> bool) -> bool
   *
   * Built-in universal quantifier.
   *)
  val all : term

  (*
   * exist : (set -> bool) -> bool
   *
   * Existential quantifier.
   *
   * Defined as: exist p = not (all x . not (p x))
   *)
  val exist : term

  (*
   * exist1 : (set -> bool) -> bool
   *
   * Unique existential quantifier.
   *
   * Defined as:
   * exist1 p = exist x . all y (p y <=> y = x)
   *)
  val exist1 : term

  (*
   * in : set -> set -> bool
   *
   * Built-in set membership operator.
   *)
  val in_c : term

  (*
   * the_only : (set -> bool) -> set
   *
   * Built-in intentional definition operator.
   *
   * The only set with the given property
   * (assuming there is exactly one such set).
   *
   * If no such set exists, or if multiple such sets
   * exists, this gives the empty set instead. This is
   * a bit of a hack to ensure this has a unique interpretation
   * given a ZFC model.
   *
   * Note that this property of the operator subsumes the
   * axiom of empty set.
   *)
  val the_only : term

  (*
   * Axiom for intensional definitions:
   *
   * exists1 p |- p (the_only p)
   *)
  val the_only_intro : theorem

  (*
   * Axiom for invalid intensional definitions.
   *
   * If a definition is invalid, the_only p is the empty set:
   *
   * not (exists1 p) |- not (x in the_only p)
   *
   * As mentioned above, this is to ensure the_only has
   * a unique interpretation in a given ZFC model.
   *)
  val the_only_invalid : theorem

end =

struct

  datatype base_type =
    Bool
  | Set
  | DefinedType of string * term

  and mf_type =
    BaseType of base_type
  | Operation of mf_type * mf_type

  and constant =
    False
  | Implies
  | Equal
  | All
  | In
  | TheOnly
  | Defined of string * mf_type * term

  and term =
    Constant of constant
  | BoundVariable of int
  | FreeVariable of string
  | Application of term * term
  | Lambda of string * mf_type * term

  (*
   * Theorem (free variables, assumptions, conclusion).
   *)
  datatype theorem =
    Theorem of (string * mf_type) list * term list * term

  (*
   * Built-in bool type.
   *)
  val bool_t = BaseType Bool

  (*
   * Built-in set type.
   *)
  val set = BaseType Set

  fun type_of_constant (c : constant) =
    case c of
      False => bool_t
    | Implies => Operation (bool_t, Operation (bool_t, bool_t))
    | Equal => Operation (set, Operation (set, bool_t))
    | All => Operation (Operation (set, bool_t), bool_t)
    | In => Operation (set, Operation (set, bool_t))
    | TheOnly => Operation (Operation (set, bool_t), set)
    | Defined (_, t, _) => t

  fun contains (l : ''a list, x : ''a) =
    case l of
      [] => false
    | (h::t) => h = x orelse contains(t, x)

  fun type_of_free_variable (name : string,
                             free_vars : (string * mf_type) list) =
    case free_vars of
      [] => raise Fail ("Unknown variable " ^ name ^ ".")
    | ((name', t)::other) =>
        if name' = name
        then t
        else type_of_free_variable(name, other)

  fun type_of_term (a : term,
                    free_vars : (string * mf_type) list,
                    bound_var_types : mf_type list) =
    case a of
      Constant c => type_of_constant c
    | BoundVariable i => List.nth (bound_var_types, i)
    | FreeVariable name => type_of_free_variable (name, free_vars)
    | Application (f, x) =>
        (case type_of_term (f, free_vars, bound_var_types) of
          Operation (t1, t2) =>
            if type_of_term (x, free_vars, bound_var_types) = t1
            then t2
            else raise Fail "Type mismatch in application."
         | _ => raise Fail "Not an operation.")
    | Lambda (_, t, v) =>
        Operation (t, type_of_term (v, free_vars, t :: bound_var_types))

  fun define_type (name : string, property : term) =
    if type_of_term (property, [], []) = Operation (set, bool_t)
    then
      BaseType (DefinedType (name, property))
    else
      raise Fail ("Definition of type " ^ name ^ "has wrong type.")

  fun define (name : string, a : term) =
    Constant (Defined (name, type_of_term (a, [], []), a))

  val false_c = Constant False

  val implies = Constant Implies

  fun apply2 (f : term, a : term, b : term) =
    Application(Application(f, a), b)

  (*
   * Define: not p = (p => false).
   *)
  val not_c =
    define("not",
      Lambda("p", bool_t,
        apply2(implies, BoundVariable 0, false_c)))

  (*
   * Define: p or q = (not p => q).
   *)
  val or_c =
    define("or",
      Lambda("p", bool_t,
        Lambda("q", bool_t,
          apply2(implies,
                 Application(not_c, BoundVariable 1),
                 BoundVariable 0))))

  (*
   * Define: p and q = not (not p or not q).
   *)
  val and_c =
    define("and",
      Lambda("p", bool_t,
        Lambda("q", bool_t,
          Application(not_c,
            apply2(or_c,
              Application(not_c, BoundVariable 1),
              Application(not_c, BoundVariable 0))))))

  (*
   * Define: p <=> q = (p => q) and (q => p).
   *)
  val iff =
    define("<=>",
      Lambda("p", bool_t,
        Lambda("q", bool_t,
          apply2(and_c,
            apply2(implies, BoundVariable 1, BoundVariable 0),
            apply2(implies, BoundVariable 0, BoundVariable 1)))))

  val equal = Constant Equal

  val all = Constant All

  (*
   * Define: exist p = not (all x . not (p x)).
   *)
  val exist =
    define("exist",
      Lambda("p", Operation(set, bool_t),
        Application(not_c,
          Application(all,
            Lambda("x", set,
              Application(not_c,
                Application(BoundVariable 1, BoundVariable 0)))))))

  (*
   * Defined: exist1 p = exist x . all y . (p y <=> y = x)
   *)
  val exist1 =
    define("exist1",
      Lambda("p", Operation(set, bool_t),
        Application(exist,
          Lambda("x", set,
            Application(all,
              Lambda("y", set,
                apply2(iff,
                  Application(BoundVariable 2, BoundVariable 0),
                  apply2(equal, BoundVariable 0, BoundVariable 1))))))))

  val in_c = Constant In

  val the_only = Constant TheOnly

  (*
   * Declare an axiom.
   *
   * Type-check just to make sure everything is type-correct.
   *)
  fun axiom(free_vars: (string * mf_type) list,
            assumptions : term list,
            conclusion : term) =
    if (List.all
        (fn a => type_of_term (a, free_vars, []) = bool_t)
        (conclusion :: assumptions))
    then
      Theorem (free_vars, assumptions, conclusion)
    else
      raise Fail "Axiom assumptions and conclusion must be bool."

  (*
   * Axiom for intensional definitions:
   *
   * exists1 p |- p (the_only p)
   *)
  val the_only_intro =
    let
      val p = ("p", Operation(set, bool_t))
      val fp = FreeVariable "p"
    in
      axiom(
        [p],
        [Application(exist1, fp)],
        Application(fp, Application(the_only, fp)))
    end

  (*
   * Axiom for invalid intensional definitions.
   *
   * not (exists1 p) |- not (x in the_only p)
   *)
  val the_only_invalid =
    let
      val p = ("p", Operation(set, bool_t))
      val fp = FreeVariable "p"
      val x = ("x", set)
      val fx = FreeVariable "x"
    in
    axiom(
      [p, x],
      [Application(not_c, Application(exist1, fp))],
      Application(
        not_c,
        apply2(in_c, fx, Application(the_only, fp))))
    end

end
