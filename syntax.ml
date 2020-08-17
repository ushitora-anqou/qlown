type exp =
  | Var of string
  | Univ of int
  | Prod of string option * exp_with_loc * exp_with_loc
  | Lam of string * exp_with_loc * exp_with_loc
  | App of exp_with_loc * exp_with_loc

and exp_with_loc = { e : exp; l : Lexing.position }

type program =
  | LetDecl of string * exp_with_loc
  | LetDef of string * exp_with_loc * exp_with_loc
  | AssumeLetDef of string * exp_with_loc * exp_with_loc
  | TypeDef of string * exp_with_loc * (string * exp_with_loc) list

type program_with_loc = { p : program; l : Lexing.position }
