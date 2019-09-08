(*
 * First-order logic signature.
 *)
signature PRIMITIVES =
sig

  (* The type of primitive types. *)
  eqtype prim_type

  (* The type of primitive symbols. *)
  eqtype symbol

  (* The type of a primitive symbol. *)
  val symbol_type : symbol -> {
    arguments : prim_type list,
    (* NONE for relation symbols, SOME for function symbols *)
    result: prim_type option
  }

  (* Name of a primitive type. *)
  val prim_type_name : prim_type -> string

  (* Name of a symbol. *)
  val symbol_name : symbol -> string

end
