signature SET_THEORY_PRIMITIVES =
sig
  include PRIMITIVES

  (* Primitive type of sets. *)
  val Set : prim_type

  (* Set membership relation. *)
  val In : symbol
end
