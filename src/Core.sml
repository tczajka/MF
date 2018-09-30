(*
 * First-order logic and ZFC axioms.
 *
 * This is the trusted logical core of the MF system.
 *
 * Because it needs to be trusted, it needs to be as simple and self-contained
 * as possible. For this reason, we are not using a parser here, since we do not
 * want the correctness of the whole system to depend on the correctness of the
 * parser. Hence we define axioms via direct syntax trees.
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
  datatype type' =
    BaseType of base_type
  | Operation of type' * type'

  (*
   * A constant.
   *
   * This is abstract so that malformed constants cannot be created.
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
  | Lambda of string * type' * term

  (*
   * A proved theorem.
   *)
  type theorem

  (*
   * The boolean type.
   *)
  val bool' : base_type

  (*
   * The set type.
   *)
  val set : base_type

  (*
   * Define a new type.
   *
   * The definition must be of type (set -> bool).
   *
   * This defines a criterion for sets (i.e. a class of sets) that belong to
   * the new type.
   *)
  val define_type : string * term -> base_type

  (*
   * Define a new constant.
   *)
  val define : string * term -> constant

  (*
   * false : bool
   *
   * Built-in.
   *)
  val false' : constant

  (*
   * => : bool -> bool -> bool
   *
   * Built-in implication operator.
   *)
  val implies : constant

  (*
   * not : bool -> bool
   *
   * Defined as: not p = p => false.
   *)
  val not' : constant

  (*
   * or : bool -> bool -> bool
   *
   * Defined as: p or q = not p => q
   *)
  val or' : constant

  (*
   * and : bool -> bool -> bool
   *
   * Defined as: p and q = not (not p or not q)
   *)
  val and' : constant

  (*
   * <=> : bool -> bool -> bool
   *
   * Defined as: p <=> q = (p => q) and (q => p).
   *)
  val iff : constant

  (*
   * = : set -> set -> bool
   *
   * Built-in set apply_equal operator.
   *)
  val equal : constant

  (*
   * /= : set -> set -> bool
   *
   * Not equal operator.
   *)
  val not_equal : constant

  (*
   * all : (set -> bool) -> bool
   *
   * Built-in universal quantifier.
   *)
  val all : constant

  (*
   * exist : (set -> bool) -> bool
   *
   * Existential quantifier.
   *
   * Defined as: exist p = not (all x . not (p x))
   *)
  val exist : constant

  (*
   * exist1 : (set -> bool) -> bool
   *
   * Unique existential quantifier.
   *
   * Defined as:
   * exist1 p = exist x . all y (p y <=> y = x)
   *)
  val exist1 : constant

  (*
   * in : set -> set -> bool
   *
   * Built-in set membership operator.
   *)
  val in' : constant

  (*
   * the_only : (set -> bool) -> set
   *
   * Built-in intentional definition operator.
   *
   * The only set with the given property
   * (assuming there is exactly one such set).
   *
   * If no such set exists, or if multiple such sets exist, this gives the empty
   * set instead. This is a bit of a hack to ensure this has a unique
   * interpretation given a ZFC model.
   *
   * Note that this property of the operator subsumes the axiom of empty set.
   *)
  val the_only : constant

  (*
   * The empty set.
   *
   * Defined in a hacky way: the only set such that ... contradiction.
   * This works because of how we defined "the_only" for contradictory criteria
   * (axiom_the_only_invalid).
   *
   * empty = the_only a . false
   *
   * This is simpler than the more obvious:
   * empty = the_only a . all x . not (x in a)
   *)
  val empty : constant

  (*
   * Subset predicate.
   *
   * subset a b = all x . x in a => x in b
   *)
  val subset : constant

  (*
   * Disjoint sets predicate.
   *
   * disjoint a b = all x . not (x in a and x in b)
   *)
  val disjoint : constant

  (*
   * Axiom for intensional definitions:
   *
   * If there is exactly one set satisfying a given criterion P, then the_only P
   * is that set.
   *
   * exist1 p |- p (the_only p)
   *)
  val axiom_the_only : theorem

  (*
   * Axiom for invalid intensional definitions.
   *
   * If a definition is invalid (there is not exactly one set satisfying
   * the criterion), the_only p is the empty set:
   *
   * not (exist1 p) |- not (x in the_only p)
   *
   * As mentioned above, this is to ensure the_only has a unique interpretation
   * in a given ZFC model, and avoids having a separate axiom of empty set.
   *)
  val axiom_the_only_invalid : theorem

  (*
   * Axiom of extensionality.
   *
   * If two sets contain same elements, they are the same set.
   *
   * all x : x in a <=> x in b |- a = b
   *)
  val axiom_extensionality : theorem

  (*
   * Axiom of union.
   *
   * For a given set a, there is a set containing all elements of elements of a
   * (and maybe more).
   *
   * exist u . all b . all x . x in b and b in a => x in u
   *)
  val axiom_union : theorem

  (*
   * Axiom of power set.
   *
   * For a given set a, there is a set containing all subsets of a (and maybe
   * more).
   *
   * exist p . all b . subset b a => b in p
   *)
  val axiom_power_set : theorem

  (*
   * Axiom of replacement.
   *
   * Given a set a and an operation f, there is a set containing exactly
   * all f(x) for x in a.
   *
   * exist b. all y . y in b <=> exist x . x in a and y = f x
   *)
  val axiom_replacement : theorem

  (*
   * Axiom of regularity.
   *
   * Every nonempty set a has a member disjoint from a.
   *
   * a /= empty |- exist x : x in a and disjoint x a 
   *)
  val axiom_regularity : theorem

  (*
   * Axiom of infinity.
   *
   * There exists a nonempty set I, such that for every element there is another
   * larger element.
   *
   * exist I .
   *   I /= empty and
   *   all x . x in I => exist y . y in I and y /= x and subset x y
   *)
  val axiom_infinity : theorem

  (*
   * Axiom of choice.
   *
   * Given a set of disjoint nonempty sets, there exists a set that has exactly
   * one element in common with each of them.
   *
   * all a . a in A => a /= empty
   * all a . all b. a in A and b in A and a /= b => disjoint a b
   * |- exist C . all a . a in A => exist1 x . x in C and x in a
   *)
  val axiom_choice : theorem

end =

struct

  datatype base_type =
    Bool
  | Set
  | DefinedType of string * term

  and type' =
    BaseType of base_type
  | Operation of type' * type'

  and constant =
    False
  | Implies
  | Equal
  | All
  | In
  | TheOnly
  | Defined of string * type' * term

  and term =
    Constant of constant
  | BoundVariable of int
  | FreeVariable of string
  | Application of term * term
  | Lambda of string * type' * term

  (*
   * Theorem (free variables, assumptions, conclusion).
   *)
  datatype theorem =
    Theorem of (string * type') list * term list * term

  (*
   * Built-in bool type.
   *)
  val bool' = Bool

  val bool_type = BaseType bool'

  (*
   * Built-in set type.
   *)
  val set = Set

  val set_type = BaseType set

  fun type_of_constant (c : constant) =
    case c of
      False => bool_type
    | Implies => Operation (bool_type, Operation (bool_type, bool_type))
    | Equal => Operation (set_type, Operation (set_type, bool_type))
    | All => Operation (Operation (set_type, bool_type), bool_type)
    | In => Operation (set_type, Operation (set_type, bool_type))
    | TheOnly => Operation (Operation (set_type, bool_type), set_type)
    | Defined (_, t, _) => t

  fun contains (l : ''a list, x : ''a) =
    case l of
      [] => false
    | (h::t) => h = x orelse contains(t, x)

  fun type_of_free_variable (name : string,
                             free_vars : (string * type') list) =
    case free_vars of
      [] => raise Fail ("Unknown variable " ^ name ^ ".")
    | ((name', t)::other) =>
        if name' = name
        then t
        else type_of_free_variable(name, other)

  fun type_of_term (a : term,
                    free_vars : (string * type') list,
                    bound_var_types : type' list) =
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
    if type_of_term (property, [], []) = Operation (set_type, bool_type)
    then
      DefinedType (name, property)
    else
      raise Fail ("Definition of type " ^ name ^ "has wrong type.")

  fun define (name : string, a : term) =
    Defined (name, type_of_term (a, [], []), a)

  val false' = False

  val implies = Implies

  fun apply2(c : constant, a : term, b : term) =
    Application(Application(Constant c, a), b)

  fun apply_implies(a : term, b : term) =
    apply2(implies, a, b)

  (*
   * Define: not p = (p => false).
   *)
  val not' =
    define("not",
      Lambda("p", bool_type,
        apply_implies(BoundVariable 0, Constant false')))

  fun apply_not(a : term) =
    Application(Constant not', a)

  (*
   * Define: p or q = (not p => q).
   *)
  val or' =
    define("or",
      Lambda("p", bool_type,
        Lambda("q", bool_type,
          apply_implies(
            apply_not(BoundVariable 1),
            BoundVariable 0
          )
        )
      )
    )

  fun apply_or(a : term, b : term) =
    apply2(or', a, b)

  (*
   * Define: p and q = not (not p or not q).
   *)
  val and' =
    define("and",
      Lambda("p", bool_type,
        Lambda("q", bool_type,
          apply_not(apply_or(apply_not(BoundVariable 1), apply_not(BoundVariable 0)))
        )
      )
    )

  fun apply_and(a : term, b : term) =
    apply2(and', a, b)

  fun apply_and_3(a : term, b : term, c : term) =
    apply_and(apply_and(a, b), c)

  (*
   * Define: p <=> q = (p => q) and (q => p).
   *)
  val iff =
    define("<=>",
      Lambda("p", bool_type,
        Lambda("q", bool_type,
          apply_and(
            apply_implies(BoundVariable 1, BoundVariable 0),
            apply_implies(BoundVariable 0, BoundVariable 1)
          )
        )
      )
    )

  fun apply_iff(a : term, b : term) =
    apply2(iff, a, b)

  val equal = Equal

  fun apply_equal(a : term, b : term) =
    apply2(equal, a, b)

  (*
   * Define a /= b  =  not (a=b).
   *)
  val not_equal =
    define("/=",
      Lambda("a", set_type,
        Lambda("b", set_type,
          apply_not(apply_equal(BoundVariable 1, BoundVariable 0))
        )
      )
    )

  fun apply_not_equal(a : term, b : term) =
    apply2(not_equal, a, b)

  val all = All

  fun apply_all(name : string, p : term) =
    Application(Constant all, Lambda(name, set_type, p))

  (*
   * Define: exist p = not (all x . not (p x)).
   *)
  val exist =
    define("exist",
      Lambda("p", Operation(set_type, bool_type),
        apply_not(apply_all("x", apply_not(
          Application(BoundVariable 1, BoundVariable 0)
        )))
      )
    )

  fun apply_exist(name : string, p : term) =
    Application(Constant exist, Lambda(name, set_type, p))

  (*
   * Defined: exist1 p = exist x . all y . (p y <=> y = x)
   *)
  val exist1 =
    define("exist1",
      Lambda("p", Operation(set_type, bool_type),
        apply_exist("x",
          apply_all("y",
            apply_iff(
              Application(BoundVariable 2, BoundVariable 0),
              apply_equal(BoundVariable 0, BoundVariable 1)
            )
          )
        )
      )
    )

  fun apply_exist1(name : string, p : term) =
    Application(Constant exist1, Lambda(name, set_type, p))

  val in' = In

  fun apply_in(a : term, b : term) =
    apply2(in', a, b)

  val the_only = TheOnly

  (*
   * Declare an axiom.
   *
   * Type-check just to make sure everything is type-correct.
   *)
  fun axiom(free_vars: (string * type') list,
            assumptions : term list,
            conclusion : term) =
    if (List.all
        (fn a => type_of_term (a, free_vars, []) = bool_type)
        (conclusion :: assumptions))
    then
      Theorem (free_vars, assumptions, conclusion)
    else
      raise Fail "Axiom assumptions and conclusion must be bool."

  (*
   * The empty set.
   *
   * Defined in a hacky way:
   * empty = the_only a . false
   *
   * axiom_the_only_invalid implies it's the empty set.
   *)
  val empty =
    define("empty",
      Application(Constant the_only, Lambda("a", set_type, Constant false'))
    )

  (*
   * Subset predicate.
   *
   * a subset b = all x . x in a => x in b
   *)
  val subset =
    define("subset",
      Lambda("a", set_type,
        Lambda("b", set_type,
          apply_all("x",
            apply_implies(
              apply_in(BoundVariable 0, BoundVariable 2),
              apply_in(BoundVariable 0, BoundVariable 1)
            )
          )
        )
      )
    )
        
  (*
   * Disjoint predicate.
   *
   * disjoint a b = all x . not (x in a and x in b)
   *)
  val disjoint =
    define("disjoint",
      Lambda("a", set_type,
        Lambda("b", set_type,
          apply_all("x",
            apply_not(
              apply_and(
                apply_in(BoundVariable 0, BoundVariable 2),
                apply_in(BoundVariable 0, BoundVariable 1)
              )
            )
          )
        )
      )
    )

  (*
   * Axiom for intensional definitions:
   *
   * exist1 p |- p (the_only p)
   *)
  val axiom_the_only =
    let
      val p = FreeVariable "p"
    in
      axiom(
        [("p", Operation(set_type, bool_type))],
        [Application(Constant exist1, p)],
        Application(p, Application(Constant the_only, p)))
    end

  (*
   * Axiom for invalid intensional definitions.
   *
   * not (exist1 p) |- not (x in the_only p)
   *)
  val axiom_the_only_invalid =
    let
      val p = FreeVariable "p"
      val x = FreeVariable "x"
    in
      axiom(
        [("p", Operation(set_type, bool_type)),
         ("x", set_type)],
        [apply_not(Application(Constant exist1, p))],
        apply_not(apply_in(x, Application(Constant the_only, p)))
      )
    end

  (*
   * Axiom of extensionality.
   *
   * all x : x in a <=> x in b |- a = b
   *)
  val axiom_extensionality =
    let
      val a = FreeVariable "a"
      val b = FreeVariable "b"
    in
      axiom(
        [("a", set_type), ("b", set_type)],
        [apply_all("x",
           apply_iff(
             apply_in(BoundVariable 0, a),
             apply_in(BoundVariable 0, b)
           )
         )],
        apply_equal(a, b)
      )
    end

  (*
   * Axiom of union.
   *
   * exist u . all b . all x . x in b and b in a => x in u
   *)
  val axiom_union =
    let
      val a = FreeVariable "a"
    in
      axiom(
        [("a", set_type)],
        [],
        apply_exist("u",
          apply_all("b",
            apply_all("x",
              apply_implies(
                apply_and(
                  apply_in(BoundVariable 0, BoundVariable 1),
                  apply_in(BoundVariable 1, a)
                ),
                apply_in(BoundVariable 0, BoundVariable 2)
              )
            )
          )
        )
      )
    end

  (*
   * Axiom of power set.
   *
   * exist p . all b . subset b a => b in p
   *)
  val axiom_power_set =
    let
      val a = FreeVariable "a"
    in
      axiom(
        [("a", set_type)],
        [],
        apply_exist("p",
          apply_all("b",
            apply_implies(
              apply2(subset, BoundVariable 0, a),
              apply_in(BoundVariable 0, BoundVariable 1)
            )
          )
        )
      )
    end

  (*
   * Axiom of replacement.
   *
   * Given a set a and an operation f, there is a set containing exactly
   * all f(x) for x in a.
   *
   * exist b. all y . y in b <=> exist x . x in a and y = f x
   *)
  val axiom_replacement =
    let
      val a = FreeVariable "a"
      val f = FreeVariable "f"
    in
      axiom(
        [("a", set_type), ("f", Operation(set_type, set_type))],
        [],
        apply_exist("b", apply_all("y",
          apply_iff(
            apply_in(BoundVariable 0, BoundVariable 1),
            apply_exist("x",
              apply_and(
                apply_in(BoundVariable 0, a),
                apply_equal(BoundVariable 1, Application(f, BoundVariable 0))
              )
            )
          )
        ))
      )
    end

  (*
   * Axiom of regularity.
   *
   * a /= empty |- exist x : x in a and disjoint x a 
   *)
  val axiom_regularity =
    let
      val a = FreeVariable "a"
    in
      axiom(
        [("a", set_type)],
        [apply_not_equal(a, Constant empty)],
        apply_exist("x",
          apply_and(
            apply_in(BoundVariable 0, a),
            apply2(disjoint, BoundVariable 0, a)
          )
        )
      )
    end

  (*
   * Axiom of infinity.
   *
   * There exists a nonempty set I, such that for every element there is another
   * larger element.
   *
   * exist I .
   *   I /= empty and
   *   all x . x in I => exist y . y in I and y /= x and subset x y
   *)
  val axiom_infinity =
    axiom(
      [],
      [],
      apply_exist("I",
        apply_and(
          apply_not_equal(BoundVariable 0, Constant empty),
          apply_all("x",
            apply_implies(
              apply_in(BoundVariable 0, BoundVariable 1),
              apply_exist("y",
                apply_and_3(
                  apply_in(BoundVariable 0, BoundVariable 2),
                  apply_not_equal(BoundVariable 0, BoundVariable 1),
                  apply2(subset, BoundVariable 1, BoundVariable 0)
                )
              )
            )
          )
        )
      )
    )

  (*
   * Axiom of choice.
   *
   * all a . a in A => a /= empty
   * all a . all b. a in A and b in A and a /= b => disjoint a b
   * |- exist C . all a . a in A => exist1 x . x in C and x in a
   *)
  val axiom_choice =
    let
      val A = FreeVariable "A"
    in
      axiom(
        [("A", set_type)],
        [
          apply_all("a",
            apply_implies(
              apply_in(BoundVariable 0, A),
              apply_not_equal(BoundVariable 0, Constant empty)
            )
          ),
          apply_all("a", apply_all("b",
            apply_implies(
              apply_and_3(
                apply_in(BoundVariable 1, A),
                apply_in(BoundVariable 0, A),
                apply_not_equal(BoundVariable 1, BoundVariable 0)
              ),
              apply2(disjoint, BoundVariable 1, BoundVariable 0)
            )
          ))
        ],
        apply_exist("C", apply_all("a",
          apply_implies(
            apply_in(BoundVariable 0, A),
            apply_exist1("x",
              apply_and(
                apply_in(BoundVariable 0, BoundVariable 2),
                apply_in(BoundVariable 0, BoundVariable 1)
              )
            )
          )
        ))
      )
    end

end
