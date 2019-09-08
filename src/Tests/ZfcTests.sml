structure ZFCTests =
struct
  structure SP = SetTheoryPrimitives
  structure S = Zfc.Syntax

  fun test_zfc () = 
    let
      val in1 = S.symbol SP.In
      val in2 = S.define ("in2", S.Constant in1)
    in
      Tests.assert (S.name_of_constant in2 = "in2");
      Tests.assert (S.type_of_constant in2 =
        S.Function (S.PrimitiveType SP.Set,
          S.Function (S.PrimitiveType SP.Set, S.Bool)))
    end

  val _ = Tests.register_test ("test_zfc", test_zfc)
end
