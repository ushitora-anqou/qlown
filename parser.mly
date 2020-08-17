%{
open Syntax
%}

%token LET FUN UNIV ASSUME TYPE COLON LPAREN RPAREN RARROW EQ SEMISEMI PIPE EOF

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
