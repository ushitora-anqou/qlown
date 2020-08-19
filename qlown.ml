module HashMap = Map.Make (String)

type term =
  | Var of int
  | GVar of string
  | App of term * term
  | Match of term * (string * int * term) list
  | Lam of typ * term (* ラムダ式 (fun 0 : T -> f) *)
  | Prod of typ * term (* 関数型 (forall 0 : T, S) *)
  | Univ of int

and typ = term

type binding = Decl of typ | Def of typ * term

type local = binding list

type global = binding HashMap.t

(* de Bruijn index で index i >= n を d シフト（加算）する。 *)
let rec shift_term (n : int) (d : int) = function
  | Var i when i >= n -> Var (i + d)
  | App (tr0, tr1) -> App (shift_term n d tr0, shift_term n d tr1)
  | Match (tr, brs) ->
      Match
        ( shift_term n d tr,
          List.map
            (fun (ctor, nvars, tr) ->
              (ctor, nvars, shift_term (n + nvars) d tr))
            brs )
  | Lam (ty, tr) -> Lam (shift_term n d ty, shift_term (n + 1) d tr)
  | Prod (ty, tr) -> Prod (shift_term n d ty, shift_term (n + 1) d tr)
  | tr -> tr

(* ` | ctor x1 x2 ... xnvars ` というパターンにある項をマッチさせる。 *)
let rec match_pattern g e ctor nvars = function
  | GVar id when ctor = id && nvars = 0 -> Some e
  | App (tr, tr') -> (
      match typeof g e tr' with
      | None -> failwith "(Fatal) input should be type checked in advance."
      | Some ty' -> match_pattern g (Def (ty', tr') :: e) ctor (nvars - 1) tr )
  | _ -> None

(* 引数で与えられた項を正規形まで完全β簡約する。 *)
and reduce_full (g : global) (e : local) = function
  | Var i -> (
      match List.nth e i with
      | Decl _ -> Var i
      | Def (_, tr) -> reduce_full g e @@ shift_term 0 (i + 1) tr )
  | GVar id -> (
      match HashMap.find id g with
      | Decl _ -> GVar id
      | Def (_, tr) -> reduce_full g e tr )
  | App (f, a) -> (
      let a' = reduce_full g e a in
      match reduce_full g e f with
      | Lam (ty, tr) ->
          shift_term 0 (-1) @@ reduce_full g (Def (ty, a') :: e) tr
      | f' -> App (f', a') )
  | Match (tr, brs) ->
      (* FIXME: Check if pattern match is exausitve. *)
      let tr = reduce_full g e tr in
      let rec aux = function
        | [] -> Match (tr, brs)
        | (ctor, nvars, tr') :: xs -> (
            match match_pattern g e ctor nvars tr with
            | None -> aux xs
            | Some e -> reduce_full g e tr' )
      in
      aux brs
  | Lam (ty, tr) ->
      let ty' = reduce_full g e ty in
      let tr' = reduce_full g (Decl ty' :: e) tr in
      Lam (ty', tr')
  | Prod (ty, tr) ->
      let ty' = reduce_full g e ty in
      let tr' = reduce_full g (Decl ty' :: e) tr in
      Prod (ty', tr')
  | tr -> tr

(* ある文脈eのもとで、項trが型tyを持つかを返す（型検査を行う）。 *)
and check_type (g : global) (e : local) (tr : term) (ty : typ) : bool =
  match typeof g e tr with
  | None -> false
  | Some ty' ->
      let ty' = reduce_full g e ty' in
      let ty = reduce_full g e ty in
      let rec aux ty' ty =
        match (ty', ty) with
        | Var i, Var i' -> i = i'
        | GVar id, GVar id' -> id = id'
        | App (f, a), App (f', a') -> aux f f' && aux a a'
        | Lam (ty, tr), Lam (ty', tr') -> aux ty ty' && aux tr tr'
        | Prod (ty, tr), Prod (ty', tr') -> aux ty ty' && aux tr tr'
        | Univ i, Univ j -> i <= j (* Univ i implies Univ j if i <= j *)
        | _ -> false
      in
      aux ty' ty

(* ある環境eのもとでの項trの型を返す。*)
and typeof (g : global) (e : local) = function
  | Var i ->
      Some
        (shift_term 0 (i + 1)
           (match List.nth e i with Decl ty -> ty | Def (ty, _) -> ty))
  | GVar id ->
      Some (match HashMap.find id g with Decl ty -> ty | Def (ty, _) -> ty)
  | Lam (ty, tr) -> (
      if not (assert_type g e ty) then None
      else
        match typeof g (Decl ty :: e) tr with
        | Some tytr -> Some (Prod (ty, tytr))
        | None -> None )
  | Prod (ty, tr) -> (
      match (typeof_type g e ty, typeof_type g (Decl ty :: e) tr) with
      | Some uty, Some utr -> Some (Univ (max uty utr))
      | _ -> None )
  | App (f, a) -> (
      match typeof g e f with
      | Some (Prod (ty, tr)) when check_type g e a ty ->
          (* 依存型に対応するためaの値をtrに代入する *)
          Some (shift_term 0 (-1) @@ reduce_full g (Def (ty, a) :: e) tr)
      | _ -> None )
  | Univ i -> Some (Univ (i + 1))
  | Match (tr, brs) ->
      let _ = typeof g e tr in
      List.fold_left
        (fun ty (ctor, nvars, tr) ->
          (* FIXME: ctorがtyのコンストラクタであることを確認する。 *)
          (* nvarsを環境に追加した上でtrを調べる。 *)
          let rec aux i e = function
            | Prod (ty, tr) when i <> 0 -> aux (i - 1) (Decl ty :: e) tr
            | GVar _ when i = 0 -> e
            | _ -> failwith "(fatal) not valid constructor"
          in
          let e =
            aux nvars e
            @@
            match HashMap.find ctor g with
            | Decl ty -> ty
            | _ -> failwith "constructor not found"
          in
          match (ty, typeof g e tr) with
          | None, Some ty' -> Some ty'
          | Some ty, Some ty' when ty = ty' -> Some ty'
          | _ -> None)
        None brs

(* 型の型を返す。*)
and typeof_type (g : global) (e : local) (t : term) =
  match typeof g e t with
  | None -> None
  | Some ty -> ( match reduce_full g e ty with Univ i -> Some i | _ -> None )

(* 引数が型であるかを返す。 *)
and assert_type (g : global) (e : local) (t : term) =
  match typeof_type g e t with None -> false | Some _ -> true

let conv g tr =
  let rec aux e d = function
    | Syntax.Var id when HashMap.mem id e -> Var (d - HashMap.find id e - 1)
    | Syntax.Var id when HashMap.mem id g -> GVar id
    | Syntax.Var id -> failwith @@ Printf.sprintf "Undefined variable: %s" id
    | Syntax.App ({ e = tr1; _ }, { e = tr2; _ }) ->
        App (aux e d tr1, aux e d tr2)
    | Syntax.Match ({ e = tr; _ }, brs) ->
        Match
          ( aux e d tr,
            List.map
              (fun ((ctor, args, { e = br; _ }) :
                     string * string list * Syntax.exp_with_loc) ->
                let rec aux' e i = function
                  | [] -> e
                  | "_" :: xs -> aux' e (i + 1) xs
                  | x :: xs -> aux' (HashMap.add x (d + i) e) (i + 1) xs
                in
                let e = aux' e 0 args in
                let nvars = List.length args in
                (ctor, nvars, aux e (d + nvars) br))
              brs )
    | Syntax.Prod (Some x, { e = ty; _ }, { e = tr; _ }) ->
        Prod (aux e d ty, aux (HashMap.add x d e) (d + 1) tr)
    | Syntax.Prod (None, { e = ty; _ }, { e = tr; _ }) ->
        Prod (aux e d ty, aux e (d + 1) tr)
    | Syntax.Lam (x, { e = ty; _ }, { e = tr; _ }) ->
        Lam (aux e d ty, aux (HashMap.add x d e) (d + 1) tr)
    | Syntax.Univ index -> Univ index
  in
  aux HashMap.empty 0 tr

let eval_one (lex : Lexing.lexbuf) (g : global) =
  let add_decl_wo_verif g id ty =
    let ty = conv g ty in
    Printf.printf "%s added (without verification)\n" id;
    HashMap.add id (Decl ty) g
  in
  let add_def_wo_verif g id ty tr =
    let ty = conv g ty in
    let tr = conv g tr in
    Printf.printf "%s added (without verification)\n" id;
    HashMap.add id (Def (ty, tr)) g
  in
  match Parser.toplevel Lexer.main lex with
  | None -> None
  | Some { p = Syntax.LetDecl (id, { e = ty; _ }); _ } ->
      Some (add_decl_wo_verif g id ty)
  | Some { p = Syntax.LetDef (id, { e = ty; _ }, { e = tr; _ }); _ } ->
      let tr = conv g tr in
      let ty = conv g ty in
      if not (check_type g [] tr ty) then failwith "type check failed";
      Printf.printf "%s added (VERIFIED)\n" id;
      Some (HashMap.add id (Def (ty, tr)) g)
  | Some { p = Syntax.AssumeLetDef (id, { e = ty; _ }, { e = tr; _ }); _ } ->
      Some (add_def_wo_verif g id ty tr)
  | Some { p = Syntax.TypeDef (id, { e = typ; _ }, seq); _ } ->
      let g = add_decl_wo_verif g id typ in
      let g =
        List.fold_left
          (fun g ((id, { e = typ; _ }) : string * Syntax.exp_with_loc) ->
            add_decl_wo_verif g id typ)
          g seq
      in
      Some g

let rec eval_all (lex : Lexing.lexbuf) (g : global) =
  match eval_one lex g with None -> g | Some g -> eval_all lex g

;;
let g =
  (* Read stdlib and get initial environment*)
  let ic = open_in "stdlib.qlown" in
  try
    let g = eval_all (Lexing.from_channel ic) HashMap.empty in
    close_in ic;
    g
  with e ->
    close_in_noerr ic;
    Printf.eprintf "Fatal error: stdlib is wrong (%s)" @@ Printexc.to_string e;
    exit 1
in

let lex = Lexing.from_channel stdin in
if not (Unix.isatty Unix.stdin) then (
  try (* Reading file *)
      eval_all lex g
  with e ->
    Printf.eprintf "Error: %s\n" @@ Printexc.to_string e;
    exit 1 )
else
  (* Reading user input *)
  let rec aux (g : global) =
    print_string "# ";
    flush stdout;
    aux
    @@
    try match eval_one lex g with None -> exit 0 | Some g -> g with
    | Parser.Error ->
        let pos = Lexing.lexeme_start lex in
        Printf.printf
          "  %s\027[1m\027[31m^\027[0m\nParse.Error:%d: syntax error.\n\n"
          (String.make pos ' ') (pos + 1);
        g
    | e ->
        Printf.printf "Error: %s\n" @@ Printexc.to_string e;
        g
  in
  aux g
