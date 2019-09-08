structure PeanoArithmetic : THEORY =
struct
  structure Syntax = Syntax(ArithmeticPrimitives)

  datatype axiom =
    AxiomZeroNotSuccessor
  | AxiomSuccessorIsBijection
  | AxiomOfInduction

  fun axiom_statement _= raise Fail "not implemented"
end
