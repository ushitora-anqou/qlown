%{
open Syntax
%}

%token LET FUN UNIV ASSUME TYPE MATCH WITH FIX RETURN AS IN COLON LPAREN RPAREN RARROW EQ SEMISEMI PIPE EOF

%token <int> INTV
%token <string> ID

%start toplevel
%type <Syntax.program_with_loc option> toplevel
%%

toplevel:
  | EOF { None }
  | LET id=ID COLON typ=Expr tr=option(LetStmtDef) SEMISEMI {
      Some (match tr with
      | Some tr -> { p=LetDef (id, typ, tr); l=$symbolstartpos }
      | None -> { p=LetDecl (id, typ); l=$symbolstartpos })
  }
  | ASSUME LET id=ID COLON typ=Expr tr=option(LetStmtDef) SEMISEMI {
      Some (match tr with
      | Some tr -> { p=AssumeLetDef (id, typ, tr); l=$symbolstartpos }
      | None -> { p=LetDecl (id, typ); l=$symbolstartpos })
  }
  | TYPE id=ID COLON typ=Expr EQ seq=list(TypeStmtBind) SEMISEMI {
      Some ({ p=TypeDef (id, typ, seq); l=$symbolstartpos })
  }

LetStmtDef:
  | EQ Expr { $2 }

TypeStmtBind:
  | PIPE id=ID COLON typ=Expr { (id, typ) }

Expr:
  | e=MatchExpr | e=FunExpr | e=FixExpr | e=ArrowType { e }

ArrowType:
  | x=ID COLON lhs=AppExpr RARROW rhs=Expr {
      { e=Prod (Some x, lhs, rhs); l=$symbolstartpos }
  }
  | lhs=AppExpr RARROW rhs=Expr { { e=Prod (None, lhs, rhs); l=$symbolstartpos } }
  | e=AppExpr { e }

FunExpr:
  | FUN id=ID COLON ty=AppExpr RARROW tr=Expr {
      { e=Lam ([(id, ty)], tr); l=$symbolstartpos }
  }
  | FUN tys=nonempty_list(FunArg) RARROW tr=Expr {
      { e=Lam (tys, tr); l=$symbolstartpos }
  }

FixExpr:
  | FIX funname=ID tys=nonempty_list(FunArg) COLON ty2=AppExpr RARROW tr=Expr {
      { e=Fix (funname, tys, ty2, tr); l=$symbolstartpos }
  }

FunArg:
  | LPAREN id=ID COLON ty=Expr RPAREN { (id, ty) }

MatchExpr:
  | MATCH tr=Expr AS x=ID IN in_ty=ID in_vars=list(ID) RETURN ret_ty=Expr WITH brs=list(MatchBranch) {
      { e=Match { tr; x; in_ty; in_vars; ret_ty; brs }; l=$symbolstartpos }
  }

MatchBranch:
  | PIPE ctor=ID args=list(ID) RARROW e=Expr { (ctor, args, e) }

AppExpr:
  | tr1=AppExpr tr2=AExpr { { e=App (tr1, tr2); l=$symbolstartpos } }
  | e=AExpr { e }

AExpr:
  | LPAREN tr=Expr RPAREN { tr }
  | id=ID { { e=Var id; l=$symbolstartpos } }
  | UNIV index=INTV { { e=Univ index; l=$symbolstartpos } }

