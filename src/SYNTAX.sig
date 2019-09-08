(*
 * Syntax of MF.
 *)
signature SYNTAX =
sig
  structure Prim : PRIMITIVES

  (*
   * The type of first-order types.
   *)
  datatype mf_type =
    Bool
  | PrimitiveType of Prim.prim_type
  | Function of mf_type * mf_type

  (*
   * A constant.
   *
   * This is abstract so that malformed constants cannot be created.
   *)
  type constant

  datatype term =
    Constant of constant
  | BoundVariable of int
  | FreeVariable of string
  | Application of term * term
  | Lambda of string * mf_type * term

  val symbol_constant : Prim.symbol -> constant

  val name_of_constant : constant -> string
  val type_of_constant : constant -> mf_type
  val definition_of_constant : constant -> term option

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
   * For any primitive type t:
   *
   * =[t] : t -> t -> bool
   *
   * Built-in equal operator.
   *)
  val equal : Prim.prim_type -> constant

  (*
   * For any primitive type t:
   *
   * /=[t] : t -> t -> bool
   *
   * Not equal operator.
   *
   * Defined as x /= y = not (x = y)
   *)
  val not_equal : Prim.prim_type -> constant

  (*
   * For any primitive type t:
   *
   * all[t] : (t -> bool) -> bool
   *
   * Built-in universal quantifier.
   *)
  val all : Prim.prim_type -> constant

  (*
   * Existential quantifier.
   *
   * For any primitive type t:
   *
   * exist[t] : (t -> bool) -> bool
   *
   * Defined as: exist p = not (all x . not (p x))
   *)
  val exist : Prim.prim_type -> constant

  (*
   * Unique existential quantifier.
   *
   * For any primitive type t:
   * exist1 : (t -> bool) -> bool
   *
   * Defined as:
   * exist1 p = exist x . all y (p y <=> y = x)
   *)
  val exist1 : Prim.prim_type -> constant

  (*
   * Built-in intentional definition operator.
   *
   * For any primitive type t:
   * the_only : t -> (t -> bool) -> t
   *
   * The only object with the given property (if it exists), otherwise the
   * default object.
   *)
  val the_only : Prim.prim_type -> constant

  datatype claim = Claim of {
    free_vars : string * mf_type list,
    assumptions : term list,
    conclusion : term
  }

end
