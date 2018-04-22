# MF: Formally verified mathematics

MF is a language of formal mathematics along with a library of mathematical proofs.

Goals of the project include:
* Simple logical core of axioms and inference rules.
* Logical system equivalent to ZFC (Zermelo-Fraenkel set theory with the axiom of choice).
* Readable proofs. All proofs must be written with human consumption in mind.
* Theorems are "safe", there are no back doors that can confuse the reader about what has been proved.
  * There is no mechanism to sneak in additional axioms or inference rules.
  * Theorem parser and printer will detect redefined concepts and will refuse to interpret or present the text of a theorem in
    an ambiguous way.
* Formalize basic branches of mathematics, such as mathematical analysis.
* Prove some difficult theorems. Hopefully we can eventually prove Fermat's Last Theorem!

Proofs are written as programs in Standard ML. Correctness is guaranteed by Standard ML's type system: "theorem" is an abstract
data type, axioms are constant of type "theorem", and inference rules are functions that return values of type "theorem". This
guarantees that all theorems have valid derivations. 

This also allows a whole spectrum of proof techniques, from directly applying basic inference rules, through automating simple
steps, all the way to computer verification of thousands of cases as in the proof of the Four Color Theorem by Kenneth Appel and
Wolfgang Haken.

This idea of using a programming language is inspired by Logic of Computable Functions by Robin Milner.

The main difference from other projects such as Isabelle and HOL Light is that we use first-order logic,
which makes our system exactly equivalent to ZFC. Higher-order systems, including Isabelle/ZF, make stronger
assumptions. This makes MF compatible with standard mathematical practice.
