(*
 * The Peano theory of arithmetic.
 *)
signature PEANO_ARITHMETIC =
sig
  include THEORY

  (* 0 is not a successor *)
  val AxiomZeroNotSuccessor : axiom

  (* Successor x = Successor y => x = y *)
  val AxiomSuccessorDifferent : axiom

  (* Induction *)
  val AxiomOfInduction : axiom
end
