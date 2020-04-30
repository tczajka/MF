(*
 * The Zermelo-Fraenkel axiomatic set theory with the Axiom of Choice.
 *)
signature ZFC =
sig
  include THEORY

  val AxiomOfEmptySet : axiom
  val AxiomOfExtensionality : axiom
  val AxiomOfUnion : axiom
  val AxiomOfPowerSet : axiom
  val AxiomOfReplacement : axiom
  val AxiomOfRegularity : axiom
  val AxiomOfInfinity : axiom
  val AxiomOfChoice : axiom
end
