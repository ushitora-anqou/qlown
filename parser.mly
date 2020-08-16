%{
open Syntax
%}

%token LET FUN UNIV COLON LPAREN RPAREN RARROW EQ SEMISEMI EOF

%token <int> INTV
%token <string> ID

%start toplevel
%type <Syntax.program_with_loc> toplevel
%%

toplevel:
  | EOF { exit 0 }
  | LET id=ID COLON typ=Expr tr=option(LetStmtDef) SEMISEMI {
      match tr with
      | Some tr -> { p=LetDef (id, typ, tr); l=$symbolstartpos }
      | None -> { p=LetDecl (id, typ); l=$symbolstartpos }
  }

LetStmtDef:
  | EQ Expr { $2 }

Expr:
  | e=FunExpr | e=ArrowType { e }

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

AppExpr:
  | tr1=AppExpr tr2=AExpr { { e=App (tr1, tr2); l=$symbolstartpos } }
  | e=AExpr { e }

AExpr:
  | LPAREN tr=Expr RPAREN { tr }
  | id=ID { { e=Var id; l=$symbolstartpos } }
  | UNIV index=INTV { { e=Univ index; l=$symbolstartpos } }
