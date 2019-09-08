(*
 * Syntax of MF.
 *)
functor Syntax (Prim : PRIMITIVES) :> SYNTAX =
struct
  structure Prim = Prim

  (*
   * The type of first-order types.
   *)
  datatype mf_type =
    Bool
  | PrimitiveType of Prim.prim_type
  | Function of mf_type * mf_type

  (*
   * A constant.
   *)
  datatype constant =
    False
  | Implies
  | Equal of Prim.prim_type
  | All of Prim.prim_type
  | TheOnly of Prim.prim_type
  | Symbol of Prim.symbol
  | Defined of string * mf_type * term

  and term =
    Constant of constant
  | BoundVariable of int
  | FreeVariable of string
  | Application of term * term
  | Lambda of string * mf_type * term

  val symbol_constant = Symbol

  (*
   * Helper function to get the type of a primitive symbol.
   *)
  fun symbol_type_rec (arguments : Prim.prim_type list,
                       result : Prim.prim_type option) : mf_type =
    case (arguments,result) of
      ([],NONE) => Bool
    | ([],SOME t) => PrimitiveType t
    | (ah :: at, _) => Function (PrimitiveType ah, symbol_type_rec (at, result))

  fun symbol_type (s : Prim.symbol) : mf_type =
    let val {arguments, result} = Prim.symbol_type s
    in symbol_type_rec (arguments, result)
    end

  fun name_of_constant (c : constant) : string =
    case c of
      False => "false"
    | Implies => "=>"
    | Equal _ => "="
    | All _ => "all"
    | TheOnly _ => "the_only"
    | Symbol s => Prim.symbol_name s
    | Defined (name, _, _) => name

  (*
   * The type of a constant.
   *)
  fun type_of_constant (c : constant) : mf_type =
    case c of
      False => Bool
    | Implies => Function (Bool, Function (Bool, Bool))
    | Equal t => Function (PrimitiveType t, Function (PrimitiveType t, Bool))
    | All t => Function (Function (PrimitiveType t, Bool), Bool)
    | TheOnly t => Function (Function (PrimitiveType t, Bool), Bool)
    | Symbol s => symbol_type s
    | Defined (_, t, _) => t

  (*
   * The definition of a constant, if it exists.
   *)
  fun definition_of_constant (c : constant) : term option =
    case c of
      Defined (_, _, def) => SOME def
    | _ => NONE

  (*
   * Helpers for define.
   *)
  fun type_of_free_variable (name : string,
                             free_vars : (string * mf_type) list) : mf_type =
    case free_vars of
      [] => raise Fail ("Unknown variable " ^ name ^ ".")
    | (name', t)::other =>
        if name' = name
        then t
        else type_of_free_variable(name, other)

  fun type_of_term (a : term,
                    free_vars : (string * mf_type) list,
                    bound_var_types : mf_type list) : mf_type =
    case a of
      Constant c => type_of_constant c
    | BoundVariable i => List.nth (bound_var_types, i)
    | FreeVariable name => type_of_free_variable (name, free_vars)
    | Application (f, x) =>
        (case type_of_term (f, free_vars, bound_var_types) of
          Function (t1, t2) =>
            if type_of_term (x, free_vars, bound_var_types) = t1
            then t2
            else raise Fail "Type mismatch in application."
         | _ => raise Fail "Not a function.")
    | Lambda (_, t, v) =>
        Function (t, type_of_term (v, free_vars, t :: bound_var_types))

  fun define (name : string, a : term) =
    Defined (name, type_of_term (a, [], []), a)

  val false' = False

  val implies = Implies

  fun apply2(c : constant, a : term, b : term) =
    Application(Application(Constant c, a), b)

  fun apply_implies(a : term, b : term) =
    apply2(implies, a, b)

  (*
   * Define: not p = (p => false).
   *)
  val not' =
    define("not",
      Lambda("p", Bool,
        apply_implies(BoundVariable 0, Constant false')))

  fun apply_not(a : term) =
    Application(Constant not', a)

  (*
   * Define: p or q = (not p => q).
   *)
  val or' =
    define("or",
      Lambda("p", Bool,
        Lambda("q", Bool,
          apply_implies(
            apply_not(BoundVariable 1),
            BoundVariable 0
          )
        )
      )
    )

  (*
   * Define: p and q = not (not p or not q).
   *)
  val and' =
    define("and",
      Lambda("p", Bool,
        Lambda("q", Bool,
          apply_not(apply2(or', apply_not(BoundVariable 1), apply_not(BoundVariable 0)))
        )
      )
    )

  (*
   * Define: p <=> q = (p => q) and (q => p).
   *)
  val iff =
    define("<=>",
      Lambda("p", Bool,
        Lambda("q", Bool,
          apply2(
            and',
            apply_implies(BoundVariable 1, BoundVariable 0),
            apply_implies(BoundVariable 0, BoundVariable 1)
          )
        )
      )
    )

  val equal = Equal

  (*
   * Define a /= b  =  not (a=b).
   *)
  fun not_equal (t : Prim.prim_type) =
    define("/=",
      Lambda("a", PrimitiveType t,
        Lambda("b", PrimitiveType t,
          apply_not(apply2(equal t, BoundVariable 1, BoundVariable 0))
        )
      )
    )

  val all = All

  fun apply_all(name : string, t : Prim.prim_type, p : term) =
    Application(Constant (all t), Lambda(name, PrimitiveType t, p))

  (*
   * Define: exist p = not (all x . not (p x)).
   *)
  fun exist (t : Prim.prim_type) =
    define("exist",
      Lambda("p", Function(PrimitiveType t, Bool),
        apply_not(apply_all("x", t, apply_not(
          Application(BoundVariable 1, BoundVariable 0)
        )))
      )
    )

  fun apply_exist(name : string, t : Prim.prim_type, p : term) =
    Application(Constant (exist t), Lambda(name, PrimitiveType t, p))

  (*
   * Defined: exist1 p = exist x . all y . (p y <=> y = x)
   *)
  fun exist1 (t : Prim.prim_type) =
    define("exist1",
      Lambda("p", Function(PrimitiveType t, Bool),
        apply_exist("x", t,
          apply_all("y", t,
            apply2(
              iff,
              Application(BoundVariable 2, BoundVariable 0),
              apply2(equal t, BoundVariable 0, BoundVariable 1)
            )
          )
        )
      )
    )

  val the_only = TheOnly

  datatype claim = Claim of {
    free_vars : string * mf_type list,
    assumptions : term list,
    conclusion : term
  }

end
