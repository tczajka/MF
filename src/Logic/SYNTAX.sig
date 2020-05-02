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
  | FreeVariable of Identifier.t
  | Application of term * term
  | Lambda of Identifier.t * mf_type * term

  val name_of_constant : constant -> Identifier.t
  val type_of_constant : constant -> mf_type
  val definition_of_constant : constant -> term option

  (*
   * Built-in constants.
   *)
  val false' : constant
  val implies : constant
  val equal : Prim.prim_type -> constant
  val all : Prim.prim_type -> constant
  val the_only : Prim.prim_type -> constant
  val symbol : Prim.symbol -> constant

  (*
   * Define a new constant.
   *)
  val define : Identifier.t * term -> constant

  (*
   * A sequent assumptions |- conclusion.
   *)
  datatype sequent = Sequent of {
    free_vars : Identifier.t * mf_type list,
    assumptions : term list,
    conclusion : term
  }

end
