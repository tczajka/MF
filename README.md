# MF: Formally verified mathematics

MF is a language of formal mathematics along with a library of mathematical proofs.

Proofs are written as programs in  Standard ML. Correctness is guaranteed by Standard ML's type system: "theorem" is an abstract
data type, axioms are constant of type "theorem", and inference rules are functions that return values of type "theorem". This
guarantees that all theorems have valid derivations. 

This also allows a whole spectrum of proof techniques, from directly applying basic inference rules, through automating simple
steps, all the way to computer verification of thousands of cases as in the proof of the Four Color Theorem by Kenneth Appel and
Wolfgang Haken.

Goals of the project include:
* A simple logical core of axioms and inference rules.
* Readable proofs. All proofs must be written with human consumption in mind.
* Theorems are "safe", there are no back doors that can confuse the reader about what has been proved.
  * There is no mechanism to sneak in additional axioms or inference rules.
  * Theorem parser and printer will detect redefined concepts and will refuse to interpret or present the text of a theorem in
    an ambiguous way.
* Formalize basic branches of mathematics, such as mathematical analysis.
* Prove some difficult theorems. Hopefully we can eventually prove Fermat's Last Theorem!

This idea of using a programming language is inspired by Logic of Computable Functions by Gordon Miller.

Higher order language as a foundation of mathematics is based on the simply typed lambda calculus by Alonzo Church.

Rules of inference are loosely inspired by HOL Light by John Harrison.

The logical core is made even simpler than that of HOL Light:
* We use a simpler set of axioms and inference rules.
* De Bruijn index notation for all variables and type variables makes the implementation of core logic even simpler.

Quantifiers such as "all" and "exist" are defined, and still don't need special syntax to be readable. They are just
function application:
`all x . 2 * x = x + x` is just parsed as `all (x . 2 * x = x + x)`, where the term in brackets is a function.

Some artificial restrictions in HOL Light don't appear in MF:
* Empty types are allowed.
* Polymorphic constants are allowed with no restrictions.
  For instance, one can define a constant "is_infinite[type] : bool" that is different for different types.
