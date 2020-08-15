module HashMap = Map.Make (String)

type term =
  | Var of int
  | App of term * term
  | Lam of typ * term (* ラムダ式 (fun 0 : T -> f) *)
  | Prod of typ * term (* 関数型 (forall 0 : T, S) *)
  | Univ of int

and typ = term

type binding = Decl of typ | Def of typ * term

type local = binding list

(* de Bruijn index で index i >= n を d シフト（加算）する。 *)
let rec shift_term (n : int) (d : int) = function
  | Var i when i >= n -> Var (i + d)
  | Var i -> Var i
  | App (tr0, tr1) -> App (shift_term n d tr0, shift_term n d tr1)
  | Lam (ty, tr) -> Lam (shift_term n d ty, shift_term (n + 1) d tr)
  | Prod (ty, tr) -> Prod (shift_term n d ty, shift_term (n + 1) d tr)
  | Univ i -> Univ i

(* 引数で与えられた項を正規形まで完全β簡約する。 *)
let rec reduce_full (e : local) = function
  | Var i -> (
      match List.nth e i with
      | Decl _ -> Var i
      | Def (_, tr) -> reduce_full e @@ shift_term 0 (i + 1) tr )
  | App (f, a) -> (
      let a' = reduce_full e a in
      match reduce_full e f with
      | Lam (ty, tr) -> shift_term 0 (-1) @@ reduce_full (Def (ty, a') :: e) tr
      | f' -> App (f', a') )
  | Lam (ty, tr) ->
      let ty' = reduce_full e ty in
      let tr' = reduce_full (Decl ty' :: e) tr in
      Lam (ty', tr')
  | Prod (ty, tr) ->
      let ty' = reduce_full e ty in
      let tr' = reduce_full (Decl ty' :: e) tr in
      Prod (ty', tr')
  | Univ i -> Univ i

(* 与えられた2つの項の正規形が、ある文脈のもとで等しいかを返す。*)
let equal_terms (e : local) (t1 : term) (t2 : term) : bool =
  reduce_full e t1 = reduce_full e t2

(* ある文脈eのもとで、項trが型tyを持つかを返す（型検査を行う）。 *)
let rec check_type (e : local) (tr : term) (ty : typ) : bool =
  match typeof e tr with Some ty' -> equal_terms e ty' ty | None -> false

(* ある環境eのもとでの項trの型を返す。*)
and typeof (e : local) = function
  | Var i ->
      Some
        (shift_term 0 (i + 1)
           (match List.nth e i with Decl ty -> ty | Def (ty, _) -> ty))
  | Lam (ty, tr) -> (
      if not (assert_type e ty) then None
      else
        match typeof (Decl ty :: e) tr with
        | Some tytr -> Some (Prod (ty, tytr))
        | None -> None )
  | Prod (ty, tr) -> (
      match (typeof_type e ty, typeof_type (Decl ty :: e) tr) with
      | Some uty, Some utr -> Some (Univ (max uty utr))
      | _ -> None )
  | App (f, a) -> (
      match typeof e f with
      | Some (Prod (ty, tr)) when check_type e a ty ->
          (* 依存型に対応するためaの値をtrに代入する *)
          Some (shift_term 0 (-1) @@ reduce_full (Def (ty, a) :: e) tr)
      | _ -> None )
  | Univ i -> Some (Univ (i + 1))

(* 型の型を返す。*)
and typeof_type (e : local) (t : term) =
  match typeof e t with
  | None -> None
  | Some ty -> ( match reduce_full e ty with Univ i -> Some i | _ -> None )

(* 引数が型であるかを返す。 *)
and assert_type (e : local) (t : term) =
  match typeof_type e t with None -> false | Some _ -> true

let conv g d tr =
  let rec aux g d = function
    | Syntax.Var id -> Var (d - HashMap.find id g - 1)
    | Syntax.App ({ e = tr1; _ }, { e = tr2; _ }) ->
        App (aux g d tr1, aux g d tr2)
    | Syntax.Prod (Some x, { e = ty; _ }, { e = tr; _ }) ->
        Prod (aux g d ty, aux (HashMap.add x d g) (d + 1) tr)
    | Syntax.Prod (None, { e = ty; _ }, { e = tr; _ }) ->
        Prod (aux g d ty, aux g (d + 1) tr)
    | Syntax.Lam (x, { e = ty; _ }, { e = tr; _ }) ->
        Lam (aux g d ty, aux (HashMap.add x d g) (d + 1) tr)
    | Syntax.Univ index -> Univ index
  in
  aux g d tr

let rec read_eval_print ic =
  let lex = Lexing.from_channel ic in
  if ic = stdin then (
    print_string "# ";
    flush stdout );
  ( try
      match Parser.toplevel Lexer.main lex with
      | { p = Syntax.LetDecl (id, { e = ty; _ }, { e = tr; _ }); _ } -> (
          let g =
            [
              (* False_ind : (P : Univ 0) -> False -> P *)
              Decl (Prod (Univ 0, Prod (Var 1, Var 1)));
              (* False : Univ 0 *)
              Decl (Univ 0);
            ]
          in
          let m = HashMap.empty in
          let m = HashMap.add "False" 0 m in
          let m = HashMap.add "False_ind" 1 m in
          let conv = conv m (HashMap.cardinal m) in
          try
            if check_type g (conv tr) (conv ty) then
              Printf.printf "%s VERIFIED\n" id
            else failwith "type check failed"
          with e ->
            Printf.printf "%s UNVERIFIED (%s)\n" id @@ Printexc.to_string e )
    with Parser.Error ->
      let pos = Lexing.lexeme_start lex in
      Printf.printf
        "  %s\027[1m\027[31m^\027[0m\nParse.Error:%d: syntax error.\n\n"
        (String.make pos ' ') (pos + 1) );
  if ic == stdin then read_eval_print ic

;;
read_eval_print stdin
