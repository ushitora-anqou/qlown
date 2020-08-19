{
let reservedWords = [
  (* Keywords *)
  ("let", Parser.LET);
  ("fun", Parser.FUN);
  ("Univ", Parser.UNIV);
  ("assume", Parser.ASSUME);
  ("type", Parser.TYPE);
  ("match", Parser.MATCH);
  ("with", Parser.WITH);
  ("fix", Parser.FIX);
]

exception Error of int
}

rule main = parse
  (* ignore spacing and newline characters *)
|  [' ' '\009' '\012']+     { main lexbuf }
| '\n' { Lexing.new_line lexbuf; main lexbuf }

| "(*" { comment lexbuf; main lexbuf }

| "-"? ['0'-'9']+
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }

| ":" { Parser.COLON }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| "->" { Parser.RARROW }
| "=>" { Parser.FATRARROW }
| "=" { Parser.EQ }
| ";;" { Parser.SEMISEMI }
| "|" { Parser.PIPE }

| ['_' 'a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| eof { Parser.EOF }
| _ { raise (Error (Lexing.lexeme_start lexbuf)) }

(* 再帰的なコメントを読み飛ばす *)
and comment = parse
| "(*" { comment lexbuf; comment lexbuf }
| "*)" { () }
| _ { comment lexbuf }
