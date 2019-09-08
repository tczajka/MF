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
   * Built-in constants.
   *)
  val false' = False
  val implies = Implies
  val equal = Equal
  val all = All
  val the_only = TheOnly
  val symbol = Symbol

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

  datatype sequent = Sequent of {
    free_vars : string * mf_type list,
    assumptions : term list,
    conclusion : term
  }

end
