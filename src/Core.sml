(*
 * First-order logic and ZFC axioms.
 *
 * Author: Tomek Czajka, 2018.
 *)

structure Core :>
sig

  (*
   * Term types, e.g. bool, set, set -> bool.
   *)
  datatype mf_type =
    Bool
  | Set
  | Operation of mf_type * mf_type

  (*
   * Variable, e.g. x : set, p : set -> bool.
   *)
  type variable = string * mf_type

  (*
   * A constant.
   *
   * This is abstract so that mal-typed constants
   * cannot be created. This saves the need for repeated
   * type-checking. Use name_of_constant, type_of_constant,
   * definition_of_constant instead.
   *
   * TODO: name_of_constant, definition_of_constant not yet
   * provided.
   *)
  type constant

  (*
   * Term, e.g. "all x . x in x".
   *)
  datatype term =
    Constant of constant
  | BoundVariable of int
  | UnboundVariable of variable
  | Application of term * term
  | Lambda of variable * term

  (*
   * A proved theorem.
   *)
  type theorem

  (*
   * Define a new constant.
   *)
  val define : string * term -> constant

  (*
   * false : bool
   *
   * Built-in.
   *)
  val c_false : constant

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
  val c_not : constant

  (*
   * or : bool -> bool -> bool
   *
   * Defined as: p or q = not p => q
   *)
  val c_or : constant

  (*
   * and : bool -> bool -> bool
   *
   * Defined as: p and q = not (not p or not q)
   *)
  val c_and : constant

  (*
   * <=> : bool -> bool -> bool
   *
   * Defined as: p <=> q = (p => q) and (q => p).
   *)
  val iff :  constant

  (*
   * = : set -> set -> bool
   *
   * Built-in set equality operator.
   *)
  val equal : constant

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
   * exist1 p = exist x . all y (p x <=> y = x)
   *)
  val exist1 : constant

  (*
   * in : set -> set -> bool
   *
   * Built-in set membership operator.
   *)
  val c_in : constant

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
  val the_only : constant

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

  datatype mf_type =
    Bool
  | Set
  | Operation of mf_type * mf_type

  type variable = string * mf_type

  datatype constant =
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
  | UnboundVariable of variable
  | Application of term * term
  | Lambda of variable * term

  datatype theorem = Theorem of term list * term

  fun type_of_constant (c : constant) =
    case c of
      False => Bool
    | Implies => Operation (Bool, Operation (Bool, Bool))
    | Equal => Operation (Set, Operation (Set, Bool))
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
            if type_of_term (c, bound_var_types) = t1
            then t2
            else raise Fail "Type mismatch in application."
         | _ => raise Fail "Not an operation.")
    | Lambda ((_, t), b) =>
        Operation (t, type_of_term (b, t :: bound_var_types))

  fun type_of_expression (a : term) = type_of_term(a, [])

  fun no_free_variables (a : term) =
    case a of
      Constant _ => true
    | BoundVariable _ => true
    | UnboundVariable _ => false
    | Application (b, c) => no_free_variables b andalso no_free_variables c
    | Lambda (_, b) => no_free_variables b

  fun define (name : string, a : term) =
    if no_free_variables a
    then
      Defined (name, type_of_expression a, a)
    else
      raise Fail ("Definition of " ^ name ^ " has free variables.")

  (*
   * Helper for constant application.
   *)
  fun apply(a : constant, b : term) =
    Application(Constant a, b)

  (*
   * Helper for constant application to two arguments.
   *)
  fun apply2(a : constant, b : term, c : term) =
    Application(apply(a, b), c)

  val c_false = False

  val implies = Implies

  (*
   * Define: not p = (p => false).
   *)
  val c_not =
    define("not",
      Lambda(("p", Bool),
        apply2(implies, BoundVariable 0, Constant c_false)))

  (*
   * Define: p or q = (not p => q).
   *)
  val c_or =
    define("or",
      Lambda(("p", Bool),
        Lambda(("q", Bool),
          apply2(implies, apply(c_not, BoundVariable 1), BoundVariable 0))))

  (*
   * Define: p and q = not (not p or not q).
   *)
  val c_and =
    define("and",
      Lambda(("p", Bool),
        Lambda(("q", Bool),
          apply(c_not,
            apply2(c_or,
              apply(c_not, BoundVariable 1),
              apply(c_not, BoundVariable 0))))))

  (*
   * Define: p <=> q = (p => q) and (q => p).
   *)
  val iff =
    define("<=>",
      Lambda(("p", Bool),
        Lambda(("q", Bool),
          apply2(c_and,
            apply2(implies, BoundVariable 1, BoundVariable 0),
            apply2(implies, BoundVariable 0, BoundVariable 1)))))

  val equal = Equal

  val all = All

  (*
   * Define: exist p = not (all x . not (p x)).
   *)
  val exist =
    define("exist",
      Lambda(("p", Operation(Set, Bool)),
        apply(c_not,
          apply(all,
            Lambda(("x", Set),
              apply(c_not,
                Application(BoundVariable 1, BoundVariable 0)))))))


  (*
   * Defined: exist1 p = exist x . all y (p x <=> y = x)
   *)
  val exist1 =
    define("exist1",
      Lambda(("p", Operation(Set, Bool)),
        apply(exist,
          Lambda(("x", Set),
            apply(all,
              Lambda(("y", Set),
                apply2(iff,
                  Application(BoundVariable 2, BoundVariable 1),
                  apply2(equal, BoundVariable 0, BoundVariable 1))))))))

  val c_in = In

  val the_only = TheOnly

  (*
   * Declare an axiom.
   *
   * Type-check just to make sure everything is type-correct.
   *)
  fun axiom(assumptions : term list, conclusion : term) =
    if (List.all
        (fn a => type_of_expression a = Bool)
        (conclusion :: assumptions))
    then
      Theorem (assumptions, conclusion)
    else
      raise Fail "Axiom assumptions and conclusion must be bool."

  (*
   * Axiom for intensional definitions:
   *
   * exists1 p |- p (the_only p)
   *)
  val the_only_intro =
    let val p = UnboundVariable("p", Operation(Set, Bool))
    in
    axiom(
      [apply(exist1, p)],
      Application(p, apply(the_only, p)))
    end

  (*
   * Axiom for invalid intensional definitions.
   *
   * not (exists1 p) |- not (x in the_only p)
   *)
  val the_only_invalid =
    let
      val p = UnboundVariable("p", Operation(Set, Bool))
      val x = UnboundVariable("x", Set)
    in
    axiom(
      [apply(c_not, apply(exist1, p))],
      apply(c_not, apply2(c_in, x, apply(the_only, p))))
    end

end
