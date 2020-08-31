type exp =
  | Var of string
  | Univ of int
  | Prod of string option * exp_with_loc * exp_with_loc
  | Lam of string * exp_with_loc * exp_with_loc
  | Fix of string * (string * exp_with_loc) list * exp_with_loc * exp_with_loc
  | App of exp_with_loc * exp_with_loc
  | Match of {
      (* match tr as x in ty y1 .. yn return ret_ty with | ctor x1 .. xm -> t *)
      tr : exp_with_loc;
      x : string;
      in_ty : string;
      in_vars : string list;
      ret_ty : exp_with_loc;
      brs : (string * string list * exp_with_loc) list;
    }

and exp_with_loc = { e : exp; l : Lexing.position }

type program =
  | LetDecl of string * exp_with_loc
  | LetDef of string * exp_with_loc * exp_with_loc
  | AssumeLetDef of string * exp_with_loc * exp_with_loc
  | TypeDef of string * exp_with_loc * (string * exp_with_loc) list

type program_with_loc = { p : program; l : Lexing.position }
