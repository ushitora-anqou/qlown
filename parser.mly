%{
open Syntax
%}

%token LET FUN UNIV ASSUME TYPE MATCH WITH FIX COLON LPAREN RPAREN RARROW FATRARROW EQ SEMISEMI PIPE EOF

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
  | LPAREN x=ID COLON lhs=Expr RPAREN RARROW rhs=Expr {
      { e=Prod (Some x, lhs, rhs); l=$symbolstartpos }
  }
  | lhs=AppExpr RARROW rhs=Expr { { e=Prod (None, lhs, rhs); l=$symbolstartpos } }
  | e=AppExpr { e }

FunExpr:
  | FUN LPAREN id=ID COLON ty=Expr RPAREN RARROW tr=Expr {
      { e=Lam (id, ty, tr); l=$symbolstartpos }
  }

FixExpr:
  | FIX funname=ID LPAREN id=ID COLON ty1=Expr RPAREN COLON ty2=Expr FATRARROW tr=Expr {
      { e=Fix (funname, id, ty1, ty2, tr); l=$symbolstartpos }
  }

MatchExpr:
  | MATCH e=Expr WITH brs=list(MatchBranch) {
      { e=Match (e, brs); l=$symbolstartpos }
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

