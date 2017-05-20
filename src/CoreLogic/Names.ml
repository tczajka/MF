type operator_associativity =
  | LeftAssociativity
  | RightAssociativity
  | NoAssociativity

type operator_precedence = int

type token_syntax =
  | RegularSyntax
  | OperatorSyntax of operator_precedence * operator_associativity
  | BinderSyntax

type identifier = string

type name = identifier * token_syntax
