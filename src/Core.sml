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
   * /= : set -> set -> bool
   *
   * Not equal operator.
   *)
  val not_equal : term

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
   * The empty set.
   *
   * Defined in a hacky way:
   * empty = the_only a . false
   *
   * the_only_invalid implies it's the empty set.
   *)
  val empty : term

  (*
   * Subset predicate.
   *
   * subset a b = all x . x in a => x in b
   *)
  val subset : term

  (*
   * Disjoint predicate.
   *
   * disjoint a b = all x . not (x in a and x in b)
   *)
  val disjoint : term

  (*
   * Axiom for intensional definitions:
   *
   * exist1 p |- p (the_only p)
   *)
  val the_only_intro : theorem

  (*
   * Axiom for invalid intensional definitions.
   *
   * If a definition is invalid, the_only p is the empty set:
   *
   * not (exist1 p) |- not (x in the_only p)
   *
   * As mentioned above, this is to ensure the_only has
   * a unique interpretation in a given ZFC model.
   *)
  val the_only_invalid : theorem

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
   * For a given set a, there is a set containing all elements of elements of a.
   *
   * a:set |- exist u . all b . all x . x in b and b in a => x in u
   *)
  val axiom_union : theorem

  (*
   * Axiom of power set.
   *
   * For a given set a, there is a set containing all subsets of a.
   *
   * a:set |- exist p . all b . subset b a => b in p
   *)
  val axiom_power_set : theorem

  (*
   * Axiom of replacement.
   *
   * Given a set a and an operation f, there is a set containing all f(x),
   * x in a.
   *
   * a:set, f:set->set |- exist b. all x . x in a => f x in b
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
   * |- exists I .
   *      I /= empty and
   *      all x . x in I => exists y . y in I and y /= x and subset x y
   *)
  val axiom_infinity : theorem

  (*
   * Axiom of choice.
   *
   * Given a set of disjoint sets, there exists a set that has exactly one
   * element in common with each of them.
   *
   * A:set,
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

  fun implication(a : term, b : term) =
    apply2(implies, a, b)

  (*
   * Define: not p = (p => false).
   *)
  val not_c =
    define("not",
      Lambda("p", bool_t,
        apply2(implies, BoundVariable 0, false_c)))

  fun negate(a : term) =
    Application(not_c, a)

  (*
   * Define: p or q = (not p => q).
   *)
  val or_c =
    define("or",
      Lambda("p", bool_t,
        Lambda("q", bool_t,
          implication(
            negate(BoundVariable 1),
            BoundVariable 0
          )
        )
      )
    )

  fun or2(a : term, b : term) =
    apply2(or_c, a, b)

  (*
   * Define: p and q = not (not p or not q).
   *)
  val and_c =
    define("and",
      Lambda("p", bool_t,
        Lambda("q", bool_t,
          negate(or2(negate(BoundVariable 1), negate(BoundVariable 0)))
        )
      )
    )

  fun and2(a : term, b : term) =
    apply2(and_c, a, b)

  fun and3(a : term, b : term, c : term) =
    and2(and2(a, b), c)

  (*
   * Define: p <=> q = (p => q) and (q => p).
   *)
  val iff =
    define("<=>",
      Lambda("p", bool_t,
        Lambda("q", bool_t,
          and2(
            implication(BoundVariable 1, BoundVariable 0),
            implication(BoundVariable 0, BoundVariable 1)
          )
        )
      )
    )

  fun iff2(a : term, b : term) =
    apply2(iff, a, b)

  val equal = Constant Equal

  fun equality(a : term, b : term) =
    apply2(equal, a, b)

  (*
   * Define a /= b  =  not (a=b).
   *)
  val not_equal =
    define("/=",
      Lambda("a", set,
        Lambda("b", set,
          negate(equality(BoundVariable 0, BoundVariable 1))
        )
      )
    )

  fun not_equality(a : term, b : term) =
    apply2(not_equal, a, b)

  val all = Constant All

  fun for_all(name : string, p : term) =
    Application(all, Lambda(name, set, p))

  (*
   * Define: exist p = not (all x . not (p x)).
   *)
  val exist =
    define("exist",
      Lambda("p", Operation(set, bool_t),
        negate(for_all("x", negate(
          Application(BoundVariable 1, BoundVariable 0)
        )))
      )
    )

  fun exists(name : string, p : term) =
    Application(exist, Lambda(name, set, p))

  (*
   * Defined: exist1 p = exist x . all y . (p y <=> y = x)
   *)
  val exist1 =
    define("exist1",
      Lambda("p", Operation(set, bool_t),
        exists("x",
          for_all("y",
            iff2(
              Application(BoundVariable 2, BoundVariable 0),
              equality(BoundVariable 0, BoundVariable 1)
            )
          )
        )
      )
    )

  fun exists1(name : string, p : term) =
    Application(exist1, Lambda(name, set, p))

  val in_c = Constant In

  fun in2(a : term, b : term) =
    apply2(in_c, a, b)

  val the_only = Constant TheOnly

  fun the(name : string, p : term) =
    Application(the_only, Lambda(name, set, p))

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
   * The empty set.
   *
   * Defined in a hacky way:
   * empty = the_only a . false
   *
   * the_only_invalid implies it's the empty set.
   *)
  val empty =
    define("empty", the("a", false_c))

  (*
   * Subset predicate.
   *
   * a subset b = all x . x in a => x in b
   *)
  val subset =
    define("subset",
      Lambda("a", set,
        Lambda("b", set,
          for_all("x",
            implication(
              in2(BoundVariable 0, BoundVariable 2),
              in2(BoundVariable 0, BoundVariable 1)
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
      Lambda("a", set,
        Lambda("b", set,
          for_all("x",
            negate(
              and2(
                in2(BoundVariable 0, BoundVariable 2),
                in2(BoundVariable 0, BoundVariable 1)
              )
            )
          )
        )
      )
    )

  (*
   * Axiom for intensional definitions:
   *
   * exists1 p |- p (the_only p)
   *)
  val the_only_intro =
    let
      val p = FreeVariable "p"
    in
      axiom(
        [("p", Operation(set, bool_t))],
        [Application(exist1, p)],
        Application(p, Application(the_only, p)))
    end

  (*
   * Axiom for invalid intensional definitions.
   *
   * not (exists1 p) |- not (x in the_only p)
   *)
  val the_only_invalid =
    let
      val p = FreeVariable "p"
      val x = FreeVariable "x"
    in
      axiom(
        [("p", Operation(set, bool_t)),
         ("x", set)],
        [negate(Application(exist1, p))],
        negate(in2(x, Application(the_only, p)))
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
        [("a", set), ("b", set)],
        [for_all("x",
           iff2(
             in2(BoundVariable 0, a),
             in2(BoundVariable 0, b)
           )
         )],
        equality(a, b)
      )
    end

  (*
   * Axiom of union.
   *
   * a:set |- exist u . all b . all x . x in b and b in a => x in u
   *)
  val axiom_union =
    let
      val a = FreeVariable "a"
    in
      axiom(
        [("a", set)],
        [],
        exists("u",
          for_all("b",
            for_all("x",
              implication(
                and2(
                  in2(BoundVariable 0, BoundVariable 1),
                  in2(BoundVariable 1, a)
                ),
                in2(BoundVariable 0, BoundVariable 2)
              )
            )
          )
        )
      )
    end

  (*
   * Axiom of power set.
   *
   * a:set |- exist p . all b . subset b a => b in p
   *)
  val axiom_power_set =
    let
      val a = FreeVariable "a"
    in
      axiom(
        [("a", set)],
        [],
        exists("p",
          for_all("b",
            implication(
              apply2(subset, BoundVariable 0, a),
              in2(BoundVariable 0, BoundVariable 1)
            )
          )
        )
      )
    end

  (*
   * Axiom of replacement.
   *
   * Given a set a and an operation f, there is a set containing all f(x),
   * x in a.
   *
   * a:set, f:set->set |- exist b. all x . x in a => f x in b
   *)
  val axiom_replacement =
    let
      val a = FreeVariable "a"
      val f = FreeVariable "f"
    in
      axiom(
        [("a", set), ("f", Operation(set, set))],
        [],
        exists("b", for_all("x",
          implication(
            in2(BoundVariable 0, a),
            in2(Application(f, BoundVariable 0), BoundVariable 1)
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
        [("a", set)],
        [not_equality(a, empty)],
        exists("x",
          and2(
            in2(BoundVariable 0, a),
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
   * |- exist I .
   *      I /= empty and
   *      all x . x in I => exist y . y in I and y /= x and subset x y
   *)
  val axiom_infinity =
    axiom(
      [],
      [],
      exists("I",
        and2(
          not_equality(BoundVariable 0, empty),
          for_all("x",
            implication(
              in2(BoundVariable 0, BoundVariable 1),
              exists("y",
                and3(
                  in2(BoundVariable 0, BoundVariable 2),
                  not_equality(BoundVariable 0, BoundVariable 1),
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
   * A:set,
   * all a . all b. a in A and b in A and a /= b => disjoint a b
   * |- exist C . all a . a in A => exist1 x . x in C and x in a
   *)
  val axiom_choice =
    let
      val A = FreeVariable "A"
    in
      axiom(
        [("A", set)],
        [
          for_all("a", for_all("b",
            implication(
              and3(
                in2(BoundVariable 1, A),
                in2(BoundVariable 0, A),
                not_equality(BoundVariable 1, BoundVariable 0)
              ),
              apply2(disjoint, BoundVariable 1, BoundVariable 0)
            )
          ))
        ],
        exists("C", for_all("a",
          implication(
            in2(BoundVariable 0, A),
            exists1("x",
              and2(
                in2(BoundVariable 0, BoundVariable 2),
                in2(BoundVariable 0, BoundVariable 1)
              )
            )
          )
        ))
      )
    end

end
