(*
 * Signature of set theory.
 *
 * One primitive type of sets:
 * set
 *
 * One primitive relation:
 * in : set -> set
 *)
structure SetTheoryPrimitives : PRIMITIVES =
struct
  open SetTheorySymbols

  fun symbol_type In = {
    arguments = [Set, Set],
    result = NONE
  }

  fun prim_type_name Set = "set"

  fun symbol_name In = "in"
end
