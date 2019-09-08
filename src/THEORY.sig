signature THEORY =
sig
  structure Syntax : SYNTAX

  type axiom

  val axiom_statement : axiom -> Syntax.term
end
