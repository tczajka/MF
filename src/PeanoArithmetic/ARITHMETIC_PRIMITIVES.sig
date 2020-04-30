(*
 * Signature of a theory of arithmetic.
 *)
signature ARITHMETIC_PRIMITIVES =
sig
  include PRIMITIVES

  (* Primitive type of natural numbers. *)
  val Natural : prim_type

  (* The 0 constant *)
  val Zero : symbol

  (* The successor function *)
  val Successor : symbol
end
