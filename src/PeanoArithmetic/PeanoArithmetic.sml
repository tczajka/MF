structure PeanoArithmetic : PEANO_ARITHMETIC =
struct
  structure Syntax = Syntax(ArithmeticPrimitives)

  datatype axiom =
    AxiomZeroNotSuccessor
  | AxiomSuccessorDifferent
  | AxiomOfInduction

  fun axiom_statement _= raise Fail "not implemented"
end
