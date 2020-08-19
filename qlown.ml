module HashMap = Map.Make (String)

(* デバッグ情報を出力するための関数。 *)
let print_debug () =
  Printf.ksprintf (fun s ->
      if false then (
        Printf.eprintf "%s" s;
        flush stderr ))

type term =
  | Var of int
  | GVar of string
  | App of term * term
  | Match of term * (string * int * term) list
  | Lam of typ * term (* ラムダ式 (fun 0 : T -> f) *)
  | Fix of typ * typ * term (* 再帰関数式 (fix 1 (0 : T) : (S) -> f *)
  | Prod of typ * term (* 関数型 (forall 0 : T, S) *)
  | Univ of int

and typ = term

type binding = Decl of typ | Def of typ * term

type local = binding list

type global = binding HashMap.t

let rec string_of_term = function
  | Var i -> Printf.sprintf "(Var %d)" i
  | GVar id -> Printf.sprintf "(GVar %s)" id
  | App (l, r) -> Printf.sprintf "(%s %s)" (string_of_term l) (string_of_term r)
  | Match (tr, brs) ->
      Printf.sprintf "(match %s with %s)" (string_of_term tr)
        ( String.concat " | "
        @@ List.map
             (fun (ctor, nvars, br) ->
               Printf.sprintf "%s (%d) -> %s" ctor nvars (string_of_term br))
             brs )
  | Lam (ty, tr) ->
      Printf.sprintf "(fun 0 : %s -> %s)" (string_of_term ty)
        (string_of_term tr)
  | Fix (ty1, ty2, tr) ->
      Printf.sprintf "(fix 0 (1 : %s) : %s -> %s)" (string_of_term ty1)
        (string_of_term ty2) (string_of_term tr)
  | Prod (ty, tr) ->
      Printf.sprintf "((0 : %s) -> %s)" (string_of_term ty) (string_of_term tr)
  | Univ i -> Printf.sprintf "(Univ %d)" i

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
  | Fix (ty1, ty2, tr) ->
      Fix (shift_term n d ty1, shift_term (n + 1) d ty2, shift_term (n + 2) d tr)
  | Prod (ty, tr) -> Prod (shift_term n d ty, shift_term (n + 1) d tr)
  | tr -> tr

(* トップレベルでde Bruijn indexでindexを指す項をすべてnewtrに置換する。*)
let rec subst index newtr = function
  | Var i when i = index -> shift_term 0 (i + 1) newtr
  | App (tr1, tr2) -> App (subst index newtr tr1, subst index newtr tr2)
  | Match (tr, brs) ->
      Match
        ( subst index newtr tr,
          List.map
            (fun (ctor, nvars, br) ->
              (ctor, nvars, subst (index + nvars) newtr br))
            brs )
  | Lam (ty, tr) -> Lam (subst index newtr ty, subst (index + 1) newtr tr)
  | Fix (ty1, ty2, tr) ->
      Fix
        ( subst index newtr ty1,
          subst (index + 1) newtr ty2,
          subst (index + 2) newtr tr )
  | Prod (ty, tr) -> Prod (subst index newtr ty, subst (index + 1) newtr tr)
  | tr -> tr

(* ` | ctor x1 x2 ... xnvars ` というパターンに入力項をマッチさせ、置換後の結果を返す。 *)
let rec match_pattern ctor nvars br tr =
  let rec aux i br = function
    | GVar id when ctor = id && i = nvars -> Some br
    | App (tr1, tr2) -> aux (i + 1) (subst i tr2 br) tr1
    | _ -> None
  in
  aux 0 br tr

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
      | Lam (_, tr) -> reduce_full g e @@ shift_term 0 (-1) @@ subst 0 a' tr
      | Fix (ty1, ty2, tr) ->
          (* 簡約は必ずとまると仮定する。 *)
          let tr' = shift_term 0 (-1) @@ subst 0 (Fix (ty1, ty2, tr)) tr in
          let tr' = shift_term 0 (-1) @@ subst 0 a' tr' in
          let tr' = reduce_full g e tr' in
          print_debug () "ty1: %s\n" @@ string_of_term ty1;
          print_debug () "ty2: %s\n" @@ string_of_term ty2;
          print_debug () "tr:  %s\n" @@ string_of_term tr;
          print_debug () "---> %s\n" @@ string_of_term tr';
          tr'
      | f' -> App (f', a') )
  | Match (tr, brs) ->
      (* FIXME: Check if pattern match is exausitve. *)
      let tr = reduce_full g e tr in
      let rec aux = function
        | [] -> Match (tr, brs)
        | (ctor, nvars, br) :: xs -> (
            match match_pattern ctor nvars br tr with
            | None -> aux xs
            | Some br -> reduce_full g e @@ shift_term 0 (-nvars) br )
      in
      aux brs
  | Lam (ty, tr) ->
      let ty' = reduce_full g e ty in
      let tr' = reduce_full g (Decl ty' :: e) tr in
      Lam (ty', tr')
  | Fix (ty1, ty2, tr) ->
      let ty1 = reduce_full g e ty1 in
      let e = Decl ty1 :: e in
      let ty2 = reduce_full g e ty2 in
      let e = Decl (Prod (ty1, ty2)) :: e in
      let tr = reduce_full g e tr in
      Fix (ty1, ty2, tr)
  | Prod (ty, tr) ->
      let ty' = reduce_full g e ty in
      let tr' = reduce_full g (Decl ty' :: e) tr in
      Prod (ty', tr')
  | tr -> tr

(* ある文脈eのもとで、項trが型tyを持つかを返す（型検査を行う）。 *)
and check_type (g : global) (e : local) (tr : term) (ty : typ) : bool =
  match typeof g e tr with
  | None ->
      print_debug () "1: %s\n" @@ string_of_term tr;
      print_debug () "2: %s\n" @@ string_of_term ty;
      false
  | Some ty' ->
      let ty' = reduce_full g e ty' in
      let ty = reduce_full g e ty in
      print_debug () "\t1: %s :\n\t    %s\n" (string_of_term tr)
        (string_of_term ty');
      print_debug () "\t2:  %s\n" @@ string_of_term ty;
      let rec aux ty' ty =
        match (ty', ty) with
        | Var i, Var i' -> i = i'
        | GVar id, GVar id' -> id = id'
        | App (f, a), App (f', a') -> aux f f' && aux a a'
        | Match (t, brs), Match (t', brs') ->
            aux t t'
            && List.for_all2
                 (fun (ctor, nvars, br) (ctor', nvars', br') ->
                   ctor = ctor' && nvars = nvars' && aux br br')
                 brs brs'
        | Lam (ty, tr), Lam (ty', tr') -> aux ty ty' && aux tr tr'
        | Fix (ty1, ty2, tr), Fix (ty1', ty2', tr') ->
            aux ty1 ty1' && aux ty2 ty2' && aux tr tr'
        | Prod (ty, tr), Prod (ty', tr') -> aux ty ty' && aux tr tr'
        | Univ i, Univ j -> i <= j (* Univ i implies Univ j if i <= j *)
        | _, Univ j -> (
            match typeof_type g e ty' with
            | None -> failwith "fatal: unreachable"
            | Some i -> i <= j )
        | _ -> false
      in
      let r = aux ty' ty in
      print_debug () "\t===> %s\n" @@ if r then "Yes" else "No";
      r

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
  | Fix (ty1, ty2, tr) ->
      (* FIXME: Check if tr will stop *)
      if not (assert_type g e ty1) then None
      else if not (assert_type g e ty2) then None
      else if check_type g (Decl (Prod (ty1, ty2)) :: Decl ty1 :: e) tr ty2 then
        Some (Prod (ty1, ty2))
      else None
  | Prod (ty, tr) -> (
      match (typeof_type g e ty, typeof_type g (Decl ty :: e) tr) with
      | Some uty, Some utr -> Some (Univ (max uty utr))
      | _ -> None )
  | App (f, a) -> (
      match typeof g e f with
      | Some (Prod (ty, tr)) when check_type g e a ty ->
          (* 依存型に対応するためaの値をtrに代入する *)
          print_debug () "f   %s\n" @@ string_of_term f;
          print_debug () "ty  %s\n" @@ string_of_term ty;
          print_debug () "tr  %s\n" @@ string_of_term tr;
          print_debug () "a   %s\n" @@ string_of_term a;
          print_debug () "res %s\n" @@ string_of_term @@ subst 0 a tr;
          Some (shift_term 0 (-1) @@ subst 0 a tr)
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
    | Syntax.Fix (funname, x, { e = ty1; _ }, { e = ty2; _ }, { e = tr; _ }) ->
        let ty1 = aux e d ty1 in
        let e = HashMap.add x d e in
        let ty2 = aux e (d + 1) ty2 in
        let e = HashMap.add funname (d + 1) e in
        let tr = aux e (d + 2) tr in
        Fix (ty1, ty2, tr)
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
