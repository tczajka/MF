structure ArithmeticPrimitives : ARITHMETIC_PRIMITIVES =
struct
  datatype prim_type = Natural
  datatype symbol = Zero | Successor

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
