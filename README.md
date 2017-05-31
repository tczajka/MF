# MF
Formally verified mathematics

MF is a language of formal mathematics along with a library of mathematical proofs.

Proofs are written in Standard ML. Correctness is guaranteed by Standard ML's type system: "theorem" is an abstract data type,
axioms are constant of type "theorem", and inference rules are functions that return values of type "theorem". This guarantees
that the only theorems 

This allows a whole spectrum of proof techniques, from directly applying basic inference rules, to automated searchers.
This idea is inspired by Logic of Computable Functions by Gordon Miller.

The language is simply-typed lambda-calculus by Church, with rules of inference loosely inspired by HOL Light by John Harrison.

Goals include:
* Simple logical core of axioms and inference rules.
* Readable proofs in the library. All proofs must be written with human-consumption in mind.
* Theorems are "safe", no back door to confuse the reader about what has been proved. Therefore:
  * There is no mechinism to sneak in additional axioms or inference rules.
  * Parsing and printing context will detect an attempt to redefine a concept with a different definition and will refuse to
    print a theorem in an ambiguous/confusing way.

The logical core is made even simpler than that of HOL Light:
* We use a simpler set of axioms and inference rules.
* De Bruijn index notation for all variables and type variables makes the implementation of core logic even simpler.

Binders such as "all" and "exist" are defined, and still don't need special syntax. They are just function application:
"all x . 2 * x = x + x" is just parsed as "all (x . 2 * x = x + x)", where the term in brackets is a lambda-expression.

Some artificial restrictions in HOL Light don't appear in MF:
* Empty types are allowed.
* Polymorphic constants are allowed with no restrictions.
  For instance, one can define a constant "is_infinite[type] : bool" that is different for different types.
