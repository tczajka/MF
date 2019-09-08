structure PeanoTests =
struct
  structure AP = ArithmeticPrimitives
  structure P = PeanoArithmetic
  structure S = P.Syntax

  fun test_peano () = 
    let
      val succ = S.symbol AP.Successor
      val zero = S.symbol AP.Zero
      val one = S.define ("one",
        S.Application (S.Constant succ, S.Constant zero))
    in
      Tests.assert (S.name_of_constant one = "one");
      Tests.assert (S.type_of_constant one = S.PrimitiveType AP.Natural)
    end

  val _ = Tests.register_test ("test_peano", test_peano)
end
