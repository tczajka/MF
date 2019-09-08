(*
 * Signature of a theory of arithmetic.
 *
 * One primitive type of natural numbers:
 * nat 
 *
 * One primitive constant of zero:
 * 0 : nat
 *
 * One primitive function:
 * successor : nat -> nat.
 *)
structure ArithmeticPrimitives : PRIMITIVES =
struct
  open ArithmeticSymbols

  fun
    symbol_type Zero = {
      arguments = [],
      result = SOME Natural
    }
  | symbol_type Successor = {
      arguments = [Natural],
      result = SOME Natural
    }

  fun prim_type_name Natural = "nat"

  fun symbol_name Zero = "0"
    | symbol_name Successor = "successor"

end
