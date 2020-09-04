module HashMap = Map.Make (String)

let debugging__now = true

(* Monad syntax for options.
   Thanks to: https://jobjo.github.io/2019/04/24/ocaml-has-some-new-shiny-syntax.html *)
let bind o f = match o with Some x -> f x | None -> None

let ( let* ) x f = bind x f

(* Usage: let* _ = ok @@ expr in ...
   Return None if expr is false. *)
let ok (b : bool) = if b then Some true else None

let mapi f l =
  let rec aux i = function [] -> [] | h :: t -> f i h :: aux (i + 1) t in
  aux 0 l

let fold_lefti f a l =
  let rec aux i a = function [] -> a | h :: t -> aux (i + 1) (f i a h) t in
  aux 0 a l

exception Unreachable

(* デバッグ情報を出力するための関数。 *)
let print_debug () =
  Printf.ksprintf (fun s ->
      if debugging__now then (
        Printf.eprintf "%s" s;
        flush stderr ))

type term =
  | Var of int
  | GVar of string
  | App of term * term
  | Match of {
      (* match tr as x in ty y1 y2 .. yn return P with | ctor x1 x2 .. xm -> t' *)
      tr : term;
      in_ty : string;
      in_nvars : int;
      ret_ty : typ;
      brs : (string * int * term) list;
    }
  | Lam of typ * term (* ラムダ式 (fun 0 : T -> f) *)
  | Fix of typ list * typ * term (* 再帰関数式 (fix n (n-1 : Tn-1) ... (0 : T0) : S -> f *)
  | Prod of typ * term (* 関数型 (forall 0 : T, S) *)
  | Univ of int

and typ = term

type binding = Decl of typ | Def of typ * term

type local = binding list

type ctor_info = {
  (* Assume  | ctor : (x1:A1) -> ... -> (xm:Am) -> ty u1 u2 .. un *)
  (* m *) nvars : int;
  (* [A1; ..; Am] *) args_types : typ list;
  (* ty *) ty_name : string;
  (* [u1; u2; .. ; un] *) ty_args : term list;
}

type world = { g : binding HashMap.t; ctor_map : ctor_info HashMap.t }

let empty_world = { g = HashMap.empty; ctor_map = HashMap.empty }

let find_ctor_info (w : world) (id : string) = HashMap.find id w.ctor_map

let find_gvar (w : world) (id : string) = HashMap.find id w.g

let rec string_of_term tr =
  let open Printf in
  match tr with
  | Var i -> sprintf "(Var %d)" i
  | GVar id -> sprintf "(GVar %s)" id
  | App (l, r) -> sprintf "(%s %s)" (string_of_term l) (string_of_term r)
  | Match { tr; in_ty; in_nvars; ret_ty; brs } ->
      sprintf "(match %s as (Var %d) in %s %sreturn %s with %s)"
        (string_of_term tr) in_nvars in_ty
        ( if in_nvars = 0 then ""
        else if in_nvars = 1 then "(Var 0) "
        else sprintf "(Var %d)..(Var %d) " (in_nvars - 1) 0 )
        (string_of_term ret_ty)
        ( String.concat " | "
        @@ List.map
             (fun (ctor, nvars, br) ->
               sprintf "%s %s-> %s" ctor
                 ( if nvars = 0 then ""
                 else if nvars = 1 then "(Var 0) "
                 else sprintf "(Var %d)..(Var %d) " (nvars - 1) 0 )
                 (string_of_term br))
             brs )
  | Lam (ty, tr) ->
      sprintf "(fun 0 : %s -> %s)" (string_of_term ty) (string_of_term tr)
  | Fix (tys, ty2, tr) ->
      sprintf "(fix _ %s : %s -> %s)"
        (String.concat " " @@ List.map string_of_term tys)
        (string_of_term ty2) (string_of_term tr)
  | Prod (ty, tr) ->
      sprintf "((0 : %s) -> %s)" (string_of_term ty) (string_of_term tr)
  | Univ i -> sprintf "(Univ %d)" i

let rec string_of_local = function
  | [] -> "[]"
  | Decl ty :: e ->
      Printf.sprintf "Decl %s :: %s" (string_of_term ty) (string_of_local e)
  | Def (ty, tr) :: e ->
      Printf.sprintf "Def (%s, %s) :: %s" (string_of_term ty)
        (string_of_term tr) (string_of_local e)

(* de Bruijn index で index i >= n を d シフト（加算）する。 *)
let rec shift_term (n : int) (d : int) = function
  | Var i when i >= n -> Var (i + d)
  | App (tr0, tr1) -> App (shift_term n d tr0, shift_term n d tr1)
  | Match { tr; in_ty; in_nvars; ret_ty; brs } ->
      Match
        {
          tr = shift_term n d tr;
          in_ty;
          in_nvars;
          ret_ty = shift_term (n + 1 + in_nvars) d ret_ty;
          brs =
            List.map
              (fun (ctor, nvars, tr) ->
                (ctor, nvars, shift_term (n + nvars) d tr))
              brs;
        }
  | Lam (ty, tr) -> Lam (shift_term n d ty, shift_term (n + 1) d tr)
  | Fix (tys, ty2, tr) ->
      let nvars = List.length tys in
      Fix
        ( mapi (fun i ty1 -> shift_term (n + i) d ty1) tys,
          shift_term (n + nvars) d ty2,
          shift_term (n + nvars + 1) d tr )
  | Prod (ty, tr) -> Prod (shift_term n d ty, shift_term (n + 1) d tr)
  | tr -> tr

(* トップレベルでde Bruijn indexでnを指す項をすべてnewtrに置換する。
   置換後の項は一般にwell-formedではない。
   基本的にはsubstのための関数だが、単体で有用な場合もある。 *)
let rec subst' n newtr = function
  | Var i when i = n -> shift_term 0 (i + 1) newtr
  | App (tr1, tr2) -> App (subst' n newtr tr1, subst' n newtr tr2)
  | Match { tr; in_ty; in_nvars; ret_ty; brs } ->
      Match
        {
          tr = subst' n newtr tr;
          in_ty;
          in_nvars;
          ret_ty = subst' (n + 1 + in_nvars) newtr ret_ty;
          brs =
            List.map
              (fun (ctor, nvars, br) ->
                (ctor, nvars, subst' (n + nvars) newtr br))
              brs;
        }
  | Lam (ty, tr) -> Lam (subst' n newtr ty, subst' (n + 1) newtr tr)
  | Fix (tys, ty2, tr) ->
      let nvars = List.length tys in
      Fix
        ( mapi (fun i ty1 -> subst' (n + i) newtr ty1) tys,
          subst' (n + nvars) newtr ty2,
          subst' (n + nvars + 1) newtr tr )
  | Prod (ty, tr) -> Prod (subst' n newtr ty, subst' (n + 1) newtr tr)
  | tr -> tr

(* de Bruijn indexで0を指す項をすべてnewtrに置換する。*)
let subst (newtr : term) (tr : term) = shift_term 0 (-1) @@ subst' 0 newtr tr

(* ` | ctor x1 x2 ... xnvars ` というパターンに入力項をマッチさせ、置換後の結果を返す。 *)
let rec match_pattern ctor nvars br tr =
  (*
    match (pair x y) with
    | pair x' y' -> y'

    ||
    ||

                                1  0 i
    ((fun x' -> (fun y' -> y')) x) y
                           br    tr
  *)
  let rec aux i = function
    | GVar id when ctor = id && i = nvars -> Some br
    | App (tr1, tr2) ->
        let* br = aux (i + 1) tr1 in
        Some (shift_term i (-1) @@ subst' i tr2 br)
    | _ -> None
  in
  aux 0 tr

(* 引数で与えられた項を正規形まで完全β簡約する。 *)
and reduce_full (w : world) (e : local) (tr : term) =
  match tr with
  | Var i -> (
      match List.nth e i with
      | Decl _ -> Var i
      | Def (_, tr) -> reduce_full w e @@ shift_term 0 (i + 1) tr )
  | GVar id -> (
      match find_gvar w id with
      | Decl _ -> GVar id
      | Def (_, tr) -> reduce_full w e tr )
  | App (f, a) -> (
      let a' = reduce_full w e a in
      match reduce_full w e f with
      | Lam (_, tr) -> reduce_full w e @@ subst a' tr
      | Fix (tys, _, tr) as fix ->
          (* 簡約は必ずとまると仮定する。 *)
          (* fix (:Tnvar-1) (:Tnvar-2) .. (:T0) : ty2 -> tr
             = fun :(Tnvar-1 -> Tnvar-2 -> ... -> T0 -> ty2) ->
                 fun :Tnvar-1 -> fun :Tnvar-2 -> ... -> fun :T0 -> tr *)
          let tr' = List.fold_right (fun ty1 tr -> Lam (ty1, tr)) tys tr in
          let tr' =
            match subst fix tr' with
            | Lam (_, tr') -> tr'
            | _ -> raise Unreachable
          in
          let tr' = reduce_full w e @@ subst a' tr' in
          print_debug () "a':  %s\n" @@ string_of_term a';
          print_debug () "fix: %s\n" @@ string_of_term fix;
          print_debug () "tr:  %s\n" @@ string_of_term tr;
          print_debug () "---> %s\n" @@ string_of_term tr';
          tr'
      | f' -> App (f', a') )
  | Match ({ tr; brs; _ } as body) ->
      (* FIXME: Check if pattern match is exausitve. *)
      let tr = reduce_full w e tr in
      (* Note that we can safely ignore `as ... in ... return ...`. *)
      (* Find matching branch and run it *)
      let rec aux = function
        | [] ->
            (* No matching branch detected. Since we assume the patterns are exhaustive,
               that means tr is not a value. *)
            Match { body with tr }
        | (ctor, nvars, br) :: brs -> (
            match match_pattern ctor nvars br tr with
            | None -> aux brs
            | Some br ->
                (* Branch found *)
                reduce_full w e br )
      in
      aux brs
  | Lam (ty, tr) ->
      let ty' = reduce_full w e ty in
      let tr' = reduce_full w (Decl ty' :: e) tr in
      Lam (ty', tr')
  | Fix (tys, ty2, tr) ->
      let e', tys =
        List.fold_left
          (fun (e, tys) ty1 -> (Decl ty1 :: e, reduce_full w e ty1 :: tys))
          (e, []) tys
      in
      let ty2 = reduce_full w e' ty2 in
      let tys_prod =
        let rec aux = function [] -> ty2 | h :: t -> Prod (h, aux t) in
        aux tys
      in
      let e =
        List.fold_left (fun e ty1 -> Decl ty1 :: e) (Decl tys_prod :: e) tys
      in
      let tr = reduce_full w e tr in
      Fix (tys, ty2, tr)
  | Prod (ty, tr) ->
      let ty' = reduce_full w e ty in
      let tr' = reduce_full w (Decl ty' :: e) tr in
      Prod (ty', tr')
  | tr -> tr

(* ある文脈eのもとで、項trが型tyを持つかを返す（型検査を行う）。 *)
and check_type (w : world) (e : local) (tr : term) (ty : typ) : bool =
  match typeof w e tr with
  | None ->
      print_debug () "CHECK TYPE typeof(tr) failed\n";
      print_debug () "\ttr: %s\n" @@ string_of_term tr;
      print_debug () "\tty: %s\n" @@ string_of_term ty;
      false
  | Some ty' ->
      let ty' = reduce_full w e ty' in
      let ty = reduce_full w e ty in
      print_debug () "CHECK TYPE\n";
      print_debug () "\ttr: %s :\n\t    %s\n" (string_of_term tr)
        (string_of_term ty');
      print_debug () "\tty: %s\n" @@ string_of_term ty;
      let rec aux ty' ty =
        match (ty', ty) with
        | Var i, Var i' -> i = i'
        | GVar id, GVar id' -> id = id'
        | App (f, a), App (f', a') -> aux f f' && aux a a'
        | ( Match { tr; in_ty; in_nvars; ret_ty; brs },
            Match
              {
                tr = tr';
                in_ty = in_ty';
                in_nvars = in_nvars';
                ret_ty = ret_ty';
                brs = brs';
              } ) ->
            (* FIXME: correct? *)
            aux tr tr' && in_ty = in_ty' && in_nvars = in_nvars'
            && aux ret_ty ret_ty'
            && List.for_all2
                 (fun (ctor, nvars, br) (ctor', nvars', br') ->
                   ctor = ctor' && nvars = nvars' && aux br br')
                 brs brs'
        | Lam (ty, tr), Lam (ty', tr') -> aux ty ty' && aux tr tr'
        | Fix (tys, ty2, tr), Fix (tys', ty2', tr') ->
            List.for_all2 (fun ty1 ty1' -> aux ty1 ty1') tys tys'
            && aux ty2 ty2' && aux tr tr'
        | Prod (ty, tr), Prod (ty', tr') -> aux ty ty' && aux tr tr'
        | Univ i, Univ j -> i <= j (* Univ i implies Univ j if i <= j *)
        | _, Univ j -> (
            match typeof_type w e ty' with
            | None -> failwith "fatal: unreachable"
            | Some i -> i <= j )
        | _ -> false
      in
      let r = aux ty' ty in
      print_debug () "\t===> %s\n" @@ if r then "Yes" else "No";
      if debugging__now && not r then failwith "check_type failed!";
      r

(* ある環境eのもとでの項trの型を返す。*)
and typeof (w : world) (e : local) (tr : term) =
  print_debug () "TYPEOF tr: %s\n" @@ string_of_term tr;
  print_debug () "       e:  %s\n" @@ string_of_local e;
  match tr with
  | Var i ->
      Some
        (shift_term 0 (i + 1)
           (match List.nth e i with Decl ty -> ty | Def (ty, _) -> ty))
  | GVar id ->
      Some (match find_gvar w id with Decl ty -> ty | Def (ty, _) -> ty)
  | Lam (ty, tr) -> (
      if not (assert_type w e ty) then None
      else
        match typeof w (Decl ty :: e) tr with
        | Some tytr -> Some (Prod (ty, tytr))
        | None -> None )
  | Fix (tys, ty2, tr) ->
      (* FIXME: Check if tr will stop *)
      (* Check if tys are actually types and get local environemnt for ty2 *)
      let rec aux e = function
        | [] -> Some e
        | ty1 :: t when assert_type w e ty1 -> aux (Decl ty1 :: e) t
        | _ -> None
      in
      let* e' = aux e tys in
      (* Check if ty2 is actually a type *)
      let* _ = ok (assert_type w e' ty2) in
      (* Type-check tr *)
      let tys_prod =
        let rec aux = function [] -> ty2 | h :: t -> Prod (h, aux t) in
        aux tys
      in
      let e =
        List.fold_left (fun e ty1 -> Decl ty1 :: e) (Decl tys_prod :: e) tys
      in
      if check_type w e tr (shift_term (List.length tys) 1 ty2) then
        Some tys_prod
      else None
  | Prod (ty, tr) -> (
      match (typeof_type w e ty, typeof_type w (Decl ty :: e) tr) with
      | Some uty, Some utr -> Some (Univ (max uty utr))
      | _ -> None )
  | App (f, a) -> (
      match typeof w e f with
      | Some (Prod (ty, tr)) when check_type w e a ty ->
          (* 依存型に対応するためaの値をtrに代入する *)
          print_debug () "\tty  %s\n" @@ string_of_term ty;
          print_debug () "\ttr  %s\n" @@ string_of_term tr;
          print_debug () "\tres %s\n" @@ string_of_term @@ subst a tr;
          Some (subst a tr)
      | _ -> None )
  | Univ i -> Some (Univ (i + 1))
  | Match { tr; in_ty; in_nvars; ret_ty; brs } ->
      (* Check if typeof(tr) : ty t1 t2 .. tn and bind ts*)
      let* typ = typeof w e tr in
      let rec aux ts = function
        | GVar in_ty' when in_ty = in_ty' -> Some ts
        | App (tr1, tr2) -> aux (tr2 :: ts) tr1
        | _ -> None
      in
      let* ts = aux [] typ in
      let* _ = ok (in_nvars = List.length ts) in
      (* FIXME: Check if ret_ty is actually a type *)
      (* Check constructors are ok *)
      if
        (* Now check if for all branch (| ctor x1 .. xm -> br),
           typeof(br) : [x->ctor x1 x2 .. xm][y1->u1][y2->u2]...[yn->un]ret_ty *)
        List.for_all
          (fun (ctor, nvars, br) ->
            let info = find_ctor_info w ctor in
            assert (in_ty = info.ty_name);
            assert (nvars = info.nvars);
            (* Get expected type of br *)
            (* x1 x2 .. xm x y1 .. yn *)
            let m, n = (nvars, List.length info.ty_args) in
            (* 1. Add x1 .. xm to Var (1 + n + m - 1) .. (1 + n) *)
            let ret_ty = shift_term (1 + n) m ret_ty in
            (* 2. Get tmp = [y1->u1]..[yn->un]ret_ty *)
            let _, tmp =
              List.fold_left
                (fun (i, ty) ui ->
                  let ui = shift_term 0 (n + 1 - i - 1) ui in
                  (i + 1, subst ui ty))
                (0, ret_ty)
              @@ List.rev info.ty_args
            in
            (* 3. Get expected type of br i.e. [x->ctor x1 x2 .. xm]tmp *)
            let expected_br_ty =
              tmp
              |> subst
                   ((* Construct `ctor x1 x2 .. xnvars`
                       i.e. `ctor (Var (nvars-1)) .. (Var 0)` *)
                    let rec aux n =
                      if n = nvars then GVar ctor else App (aux (n + 1), Var n)
                    in
                    aux 0)
            in
            (* Get environment for br *)
            let e =
              List.fold_left (fun e ty -> Decl ty :: e) e info.args_types
            in

            (* Check if correct *)
            check_type w e br expected_br_ty)
          brs
      then
        (* return [x->t][y1->t1]...[yn->tn]ret_ty *)
        (* Get tmp = [y1->t1]...[yn->tn]ret_ty *)
        let n = List.length ts in
        let _, tmp =
          List.fold_left
            (fun (i, ty) ti ->
              let ti = shift_term 0 (1 + n - i - 1) ti in
              (i + 1, subst ti ty))
            (0, ret_ty)
          @@ List.rev ts
        in
        (* Get [x->t]tmp *)
        Some (subst tr tmp)
      else None

(* 型の型を返す。*)
and typeof_type (w : world) (e : local) (t : term) =
  match typeof w e t with
  | None -> None
  | Some ty -> ( match reduce_full w e ty with Univ i -> Some i | _ -> None )

(* 引数が型であるかを返す。 *)
and assert_type (w : world) (e : local) (t : term) =
  match typeof_type w e t with None -> false | Some _ -> true

let conv (w : world) (tr : Syntax.exp) =
  let rec aux e d = function
    | Syntax.Var id when HashMap.mem id e -> Var (d - HashMap.find id e - 1)
    | Syntax.Var id when HashMap.mem id w.g -> GVar id
    | Syntax.Var id -> failwith @@ Printf.sprintf "Undefined variable: %s" id
    | Syntax.App ({ e = tr1; _ }, { e = tr2; _ }) ->
        App (aux e d tr1, aux e d tr2)
    | Syntax.Match
        {
          tr = { e = tr; _ };
          x;
          in_ty;
          in_vars;
          ret_ty = { e = ret_ty; _ };
          brs;
        } ->
        Match
          {
            tr = aux e d tr;
            in_ty;
            in_nvars = List.length in_vars;
            ret_ty =
              (let e = if x = "_" then e else HashMap.add x d e in
               let d, e =
                 List.fold_left
                   (fun (i, e) yi ->
                     if yi = "_" then (i + 1, e) else (i + 1, HashMap.add yi i e))
                   (d + 1, e)
                   in_vars
               in
               aux e d ret_ty);
            brs =
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
                brs;
          }
    | Syntax.Prod (Some x, { e = ty; _ }, { e = tr; _ }) ->
        Prod (aux e d ty, aux (HashMap.add x d e) (d + 1) tr)
    | Syntax.Prod (None, { e = ty; _ }, { e = tr; _ }) ->
        Prod (aux e d ty, aux e (d + 1) tr)
    | Syntax.Lam ([], { e = tr; _ }) -> aux e d tr
    | Syntax.Lam ((x, { e = ty; _ }) :: t, tr) ->
        Lam (aux e d ty, aux (HashMap.add x d e) (d + 1) (Syntax.Lam (t, tr)))
    | Syntax.Fix (funname, tys, { e = ty2; _ }, { e = tr; _ }) ->
        (* fix funname (x1:T1) (x2:T2) .. (xn:Tn) : ty2 -> tr *)
        let tys =
          List.map (fun ((x, e) : string * Syntax.exp_with_loc) -> (x, e.e)) tys
        in
        let rec aux' i e = function
          | [] -> (e, [])
          | (x, ty) :: t ->
              let ty = aux e (d + i) ty in
              let e, tys = aux' (i + 1) (HashMap.add x (d + i) e) t in
              (e, ty :: tys)
        in
        let e', tys' = aux' 0 e tys in
        let ty2 = aux e' (d + List.length tys') ty2 in
        let e = HashMap.add funname d e in
        let e =
          fold_lefti (fun i e (x, _) -> HashMap.add x (d + 1 + i) e) e tys
        in
        let tr = aux e (d + 1 + List.length tys') tr in
        Fix (tys', ty2, tr)
    | Syntax.Univ index -> Univ index
  in
  aux HashMap.empty 0 tr

let eval_one (lex : Lexing.lexbuf) (w : world) =
  let add_decl_wo_verif w id ty =
    let ty = conv w ty in
    Printf.printf "%s added (without verification)\n" id;
    { w with g = HashMap.add id (Decl ty) w.g }
  in
  let add_def_wo_verif w id ty tr =
    let ty = conv w ty in
    let tr = conv w tr in
    Printf.printf "%s added (without verification)\n" id;
    { w with g = HashMap.add id (Def (ty, tr)) w.g }
  in
  match Parser.toplevel Lexer.main lex with
  | None -> None
  | Some { p = Syntax.LetDecl (id, { e = ty; _ }); _ } ->
      Some (add_decl_wo_verif w id ty)
  | Some { p = Syntax.LetDef (id, { e = ty; _ }, { e = tr; _ }); _ } ->
      let tr = conv w tr in
      let ty = conv w ty in
      if not (check_type w [] tr ty) then failwith "type check failed";
      Printf.printf "%s added (VERIFIED)\n" id;
      Some { w with g = HashMap.add id (Def (ty, tr)) w.g }
  | Some { p = Syntax.AssumeLetDef (id, { e = ty; _ }, { e = tr; _ }); _ } ->
      Some (add_def_wo_verif w id ty tr)
  | Some { p = Syntax.TypeDef (ty_name, { e = typ; _ }, seq); _ } ->
      (* FIXME: Check if it satisfies positivity condition *)
      let w = add_decl_wo_verif w ty_name typ in
      Some
        (List.fold_left
           (fun w ((id, { e = typ; _ }) : string * Syntax.exp_with_loc) ->
             let typ' = conv w typ in
             let info =
               {
                 nvars =
                   (let rec aux n = function
                      | Prod (_, tr) -> aux (n + 1) tr
                      | _ -> n
                    in
                    aux 0 typ');
                 args_types =
                   (let rec aux = function
                      | Prod (ty, tr) -> ty :: aux tr
                      | _ -> []
                    in
                    aux typ');
                 ty_name;
                 ty_args =
                   (let rec aux1 args = function
                      | GVar ty_name' when ty_name = ty_name' -> args
                      | App (t1, t2) -> aux1 (t2 :: args) t1
                      | _ -> failwith "Invalid constructor definition"
                    in
                    let rec aux2 = function
                      | Prod (_, tr) -> aux2 tr
                      | ty -> ty
                    in
                    aux1 [] (aux2 typ'));
               }
             in
             let w = add_decl_wo_verif w id typ in
             { w with ctor_map = HashMap.add id info w.ctor_map })
           w seq)

let rec eval_all (lex : Lexing.lexbuf) (w : world) =
  match eval_one lex w with None -> w | Some w -> eval_all lex w

;;
let w =
  (* Read stdlib and get initial environment*)
  let ic = open_in "stdlib.qlown" in
  try
    let w = eval_all (Lexing.from_channel ic) empty_world in
    close_in ic;
    w
  with e ->
    close_in_noerr ic;
    Printf.eprintf "Fatal error: stdlib is wrong (%s)" @@ Printexc.to_string e;
    exit 1
in

let lex = Lexing.from_channel stdin in
if not (Unix.isatty Unix.stdin) then (
  try (* Reading file *)
      eval_all lex w
  with e ->
    Printf.eprintf "Error: %s\n" @@ Printexc.to_string e;
    exit 1 )
else
  (* Reading user input *)
  let rec aux w =
    print_string "# ";
    flush stdout;
    aux
    @@
    try match eval_one lex w with None -> exit 0 | Some w -> w with
    | Parser.Error ->
        let pos = Lexing.lexeme_start lex in
        Printf.printf
          "  %s\027[1m\027[31m^\027[0m\nParse.Error:%d: syntax error.\n\n"
          (String.make pos ' ') (pos + 1);
        w
    | e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        if Printexc.backtrace_status () then Printexc.print_backtrace stdout
        else Printf.printf "Set OCAMLRUNPARAM=b\n";
        w
  in
  aux w
