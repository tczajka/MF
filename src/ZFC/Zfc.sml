(*
 * The Zermelo-Fraenkel axiomatics of set theory with the Axiom of Choice.
 *)
structure Zfc : ZFC =
struct
  structure Syntax = Syntax(SetTheoryPrimitives)

  datatype axiom =
    AxiomOfEmptySet
  | AxiomOfExtensionality
  | AxiomOfUnion
  | AxiomOfPowerSet
  | AxiomOfReplacement
  | AxiomOfRegularity
  | AxiomOfInfinity
  | AxiomOfChoice

  fun axiom_statement _ = raise Fail "not implemented"
end
