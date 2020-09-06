#!/bin/bash

function fail() {
    echo -ne "\e[1;31m[ERROR]\e[0m "
    echo "$1"
    exit 1
}

dune build || fail "Build failed"
QLOWN=_build/default/qlown.exe

function test_positive() {
    res=$(echo "$1" | env OCAMLRUNPARAM=b $QLOWN 2>&1)
    if [ $? -ne 0 ]; then
        echo "$res"
        fail "$1"
    fi
}

test_positive "
    let f : P:Univ 0 -> P -> P =
      fun P:Univ 0 -> fun x:P -> x;;
"

test_positive "
    let f : P:Univ 0 -> Q:Univ 0 -> P -> Q -> P =
      fun P:Univ 0 -> fun Q:Univ 0 -> fun x:P -> fun y:Q -> x;;
"

test_positive "
    let f : P:Univ 0 -> False -> P = fun P:Univ 0 -> fun x:False -> False_ind P x;;
"

test_positive "
    let f : P:Univ 0 -> P -> (P -> False) -> False =
      fun P:Univ 0 -> fun x:P -> fun y:(P -> False) -> y x;;
"

test_positive "
    let f : A:Univ 0 -> x:A -> y:A -> eq A x y -> eq A y x =
      fun A:Univ 0 -> fun x:A -> fun y:A -> fun e:eq A x y ->
        eq_subst A x y e (fun z:A -> eq A z x) (eq_refl A x)
    ;;
"

test_positive "
    let f : A:Univ 0 -> x:A -> y:A -> z:A ->
            eq A x y -> eq A y z -> eq A x z =
      fun A:Univ 0 -> fun x:A -> fun y:A -> fun z:A ->
      fun e1:eq A x y -> fun e2:eq A y z ->
        eq_subst A y z e2 (fun w:A -> eq A x w) e1
    ;;
"

test_positive "
    let f : eq (Univ 1) (Univ 0) (Univ 0) = eq_refl (Univ 1) (Univ 0);;
"

test_positive "
    let plus1ifnonzero : nat -> nat = fun n:nat ->
      match n as n in nat return nat with
      | O -> O
      | S n' -> S n
    ;;
    let f : eq nat (plus1ifnonzero (S O)) (S (S O)) = eq_refl nat (S (S O));;
"

test_positive "
    let f : eq nat (add (S (S O)) (S O)) (S (S (S O))) = eq_refl nat (S (S (S O)));;
"

test_positive "
    let f : n:nat -> eq nat (add n O) n =
      nat_rect (fun n:nat -> eq nat (add n O) n)
               (eq_refl nat O)
               (fun n:nat -> fun H:eq nat (add n O) n -> f_apply nat nat (add n O) n H S)
    ;;
"

test_positive "
    type day : Univ 0 =
      | monday : day
      | tuesday : day
      | wednesday : day
      | thursday : day
      | friday : day
      | saturday : day
      | sunday : day
    ;;
    let next_weekday : day -> day = fun d:day ->
      match d as _ in day return day with
      | monday -> tuesday
      | tuesday -> wednesday
      | wednesday -> thursday
      | thursday -> friday
      | friday -> monday
      | saturday -> monday
      | sunday -> monday
    ;;
    let test_next_weekday : eq day (next_weekday (next_weekday saturday)) tuesday =
      eq_refl day tuesday
    ;;
"

test_positive "
    let plus_O_n : n:nat -> eq nat (add O n) n =
      fun n:nat -> eq_refl nat n
    ;;
"

test_positive "
    let plus_id_example : n:nat -> m:nat -> eq nat n m -> eq nat (add n n) (add m m) =
      fun n:nat -> fun m:nat -> fun e:eq nat n m ->
      eq_subst nat n m e (fun k:nat -> eq nat (add n n) (add k k)) (eq_refl nat (add n n))
    ;;

    (*
    Inductive eq : forall (A : Type) (x : A), A -> Prop := eq_refl : forall (A:Type) (x:A), eq A x x.
    fun (n : nat) (m : nat) (e : eq nat n m) =>
      match e as _ in eq _ n m return eq nat (n+n) (m+m) with
      | eq_refl _ n => eq_refl nat (n+n)
      end
    *)
"

test_positive "
    let plus_1_neq_0 : n:nat -> eq bool (eqb (add n (S O)) O) false =
      fun n:nat ->
        match n as n in nat return eq bool (eqb (add n (S O)) O) false with
        | O -> eq_refl bool false
        | S n' -> eq_refl bool false
    ;;
"

test_positive "
    let minus_diag : n:nat -> eq nat (minus n n) O =
      fix F (n:nat) : eq nat (minus n n) O ->
        match n as n in nat return eq nat (minus n n) O with
        | O -> eq_refl nat O
        | S n' -> F n'
    ;;
"

test_positive "
    let mult_O_plus : n:nat -> m:nat -> eq nat (mult (add O n) m) (mult n m) =
      fun n:nat -> fun m:nat -> eq_refl nat (mult n m)
    ;;
"

test_positive "
    let plus_rearrange : n:nat -> m:nat -> p:nat -> q:nat ->
                         eq nat (add (add n m) (add p q)) (add (add m n) (add p q)) =
      fun n:nat -> fun m:nat -> fun p:nat -> fun q:nat ->
        f_apply nat nat (add n m) (add m n) (nat_plus_comm n m)
                (fun k:nat -> add k (add p q))
    ;;
"

test_positive "
    type natprod : Univ 0 =
    | pair : nat -> nat -> natprod
    ;;
    let fst : natprod -> nat =
      fun p:natprod ->
        match p as _ in natprod return nat with
        | pair x _ -> x
    ;;
    let snd : natprod -> nat =
      fun p:natprod ->
        match p as _ in natprod return nat with
        | pair _ y -> y
    ;;
    let snd_correct : n:nat -> m:nat -> eq nat m (snd (pair n m)) =
      fun n:nat -> fun m:nat -> eq_refl nat m
    ;;
    let surjective_pairing : n:nat -> m:nat ->
                             eq natprod (pair n m)
                                        (pair (fst (pair n m)) (snd (pair n m))) =
      fun n:nat -> fun m:nat -> eq_refl natprod (pair n m)
    ;;
"

test_positive "
    type natlist : Univ 0 =
    | nil : natlist
    | cons : n:nat -> l:natlist -> natlist
    ;;
    let length : natlist -> nat =
      fix F (l:natlist) : nat ->
        match l as _ in natlist return nat with
        | nil -> O
        | cons _ t -> S (F t)
    ;;
    let tl : natlist -> natlist = fun l:natlist ->
      match l as _ in natlist return natlist with
      | nil -> nil
      | cons _ t -> t
    ;;
    let app : natlist -> natlist -> natlist =
      fix F (l1:natlist) : (natlist -> natlist) -> fun l2:natlist ->
        match l1 as _ in natlist return natlist with
        | nil -> l2
        | cons h t -> cons h (F t l2)
    ;;
    let nil_app : l:natlist -> eq natlist (app nil l) l =
      fun l:natlist -> eq_refl natlist l
    ;;
    let tl_length_pred : l:natlist -> eq nat (nat_pred (length l)) (length (tl l)) =
      fun l:natlist ->
        match l as l in natlist return eq nat (nat_pred (length l)) (length (tl l)) with
        | nil -> eq_refl nat O
        | cons _ t -> eq_refl nat (length t)
    ;;
    let app_assoc : l1:natlist -> l2:natlist -> l3:natlist ->
                    eq natlist (app (app l1 l2) l3) (app l1 (app l2 l3)) =
      fix F (l1:natlist) : (l2:natlist -> l3:natlist -> eq natlist (app (app l1 l2) l3) (app l1 (app l2 l3))) ->
        fun l2:natlist -> fun l3:natlist ->
          match l1 as l1 in natlist return eq natlist (app (app l1 l2) l3) (app l1 (app l2 l3)) with
          | nil -> eq_refl natlist (app l2 l3)
          | cons h t -> f_apply natlist natlist (app (app t l2) l3) (app t (app l2 l3)) (F t l2 l3) (cons h)
    ;;
    let rev : natlist -> natlist =
      fix F (l:natlist) : natlist ->
        match l as _ in natlist return natlist with
        | nil -> nil
        | cons h t -> app (F t) (cons h nil)
    ;;
    let app_length : l1:natlist -> l2:natlist ->
                     eq nat (length (app l1 l2)) (add (length l1) (length l2)) =
      fix F (l1:natlist) : (l2:natlist -> eq nat (length (app l1 l2)) (add (length l1) (length l2))) ->
      fun l2:natlist ->
        match l1 as l1 in natlist return eq nat (length (app l1 l2)) (add (length l1) (length l2)) with
        | nil -> eq_refl nat (length l2)
        | cons h t -> f_apply nat nat (length (app t l2)) (add (length t) (length l2)) (F t l2) S
    ;;
    let rev_length : l:natlist -> eq nat (length (rev l)) (length l) =
      fix F (l:natlist) : eq nat (length (rev l)) (length l) ->
        match l as l in natlist return eq nat (length (rev l)) (length l) with
        | nil -> eq_refl nat O
        | cons h t ->
          (*
            length (rev (cons h t)) = length (app (rev t) (cons h nil))
                                        BY app_length
                                    = add (length (rev t)) (length (cons h nil)) = add (length (rev t)) (S O)
                                    BY IH (with f_apply)
                                    = add (length t) (S O)
                                        BY nat_plus_comm
                                    = add (S O) (length t) = S (length t) = length (cons h t)
          *)
          eq_trans nat
            (length (rev (cons h t)))
            (add (length t) (S O))
              (*BY*) (eq_trans nat
                        (length (rev (cons h t)))
                        (add (length (rev t)) (length (cons h nil)))
                          (*BY*) (app_length (rev t) (cons h nil))
                        (add (length t) (S O))
                          (*BY*) (f_apply nat nat (length (rev t)) (length t) (F t) (fun x:nat -> add x (S O))))
            (add (S O) (length t))
              (*BY*) (nat_plus_comm (length t) (S O))
    ;;
"

test_positive "
    let hoge : X:Univ 0 -> l1:list X ->
      fun (X:Univ 0) (l1:list X) ->
        match l1 as l1 in list X return eq (list X) l1 l1 with
        | nil X -> eq_refl X (nil X)
        | cons X h t -> eq_refl X (cons X h t)
    ;;
"

test_positive "
    let test_repeat1 : eq (list nat)
                          (list_repeat nat (S(S(S(S O)))) (S(S O)))
                          (cons nat (S(S(S(S O)))) (cons nat (S(S(S(S O)))) (nil nat))) =
      eq_refl (list nat) (cons nat (S(S(S(S O)))) (cons nat (S(S(S(S O)))) (nil nat)))
    ;;
    let test_repeat2 : eq (list bool)
                          (list_repeat bool false (S O))
                          (cons bool false (nil bool)) =
      eq_refl (list bool) (cons bool false (nil bool))
    ;;
    let nil_app : X:Univ 0 -> l:list X -> eq (list X) (list_app X (nil X) l) l =
      fun X:Univ 0 -> fun l:list X -> eq_refl (list X) l
    ;;
"

test_positive "
    let snd_correct : n:nat -> m:nat -> eq nat m (prod_snd nat nat (pair nat nat n m)) =
      fun n:nat -> fun m:nat -> eq_refl nat m
    ;;
    let surjective_pairing :
      X:Univ 0 -> Y:Univ 0 -> x:X -> y:Y ->
      eq (prod X Y) (pair X Y x y)
                    (pair X Y (prod_fst X Y (pair X Y x y)) (prod_snd X Y (pair X Y x y))) =
      fun X:Univ 0 -> fun Y:Univ 0 -> fun x:X -> fun y:Y -> eq_refl (prod X Y) (pair X Y x y)
    ;;
"

test_positive "
    let nth_error : X:Univ 0 -> list X -> nat -> option X =
      fix F (X:Univ 0) (l:list X) (n:nat) : option X ->
        match l as _ in list X return option X with
        | nil X -> None X
        | cons X a l' -> match n as _ in nat return option X with
                         | O -> Some X a
                         | S n' -> F X l' n'
    ;;
    let test_index1 : eq (option nat) (nth_error nat
                                                 (cons nat (S(S(S(S O))))
                                                 (cons nat (S(S(S(S(S O)))))
                                                 (cons nat (S(S(S(S(S(S O))))))
                                                 (cons nat (S(S(S(S(S(S(S O)))))))
                                                 (nil nat)))))
                                                 O)
                                      (Some nat (S(S(S(S O))))) =
      eq_refl (option nat) (Some nat (S(S(S(S O)))))
    ;;
    let test_index3 : eq (option bool) (nth_error bool
                                                  (cons bool true
                                                  (nil bool))
                                                  (S(S O)))
                                       (None bool) =
      eq_refl (option bool) (None bool)
    ;;
"

test_positive "
    let S_injective : n:nat -> m:nat -> eq nat (S n) (S m) -> eq nat n m =
      fun (n:nat) (m:nat) (e:eq nat (S n) (S m)) ->
        eq_subst nat (S n) (S m) e (fun x:nat -> eq nat n (nat_pred x)) (eq_refl nat n)
    ;;
"

test_positive "
    let double : nat -> nat = fix F (n:nat) : nat ->
      match n as _ in nat return nat with
      | O -> O
      | S n' -> S (S (F n'))
    ;;
    let neq_nat_lemma : n:nat -> eq nat O (S n) -> False =
      fun (n:nat) (e:eq nat O (S n)) ->
        eq_subst nat O (S n) e
                 (fun n:nat -> match n as _ in nat return Univ 0 with
                               | O -> True
                               | S _ -> False)
                 I
    ;;
    let neq_nat_lemma2 : n:nat -> eq nat (S n) O -> False =
      fun (n:nat) (e:eq nat (S n) O) ->
        eq_subst nat (S n) O e
                     (fun n:nat -> match n as _ in nat return Univ 0 with
                                  | O -> False
                                  | S _ -> True)
                     I
    ;;
    let S_injective : n:nat -> m:nat -> eq nat (S n) (S m) -> eq nat n m =
      fun (n:nat) (m:nat) (e:eq nat (S n) (S m)) ->
        eq_subst nat (S n) (S m) e (fun x:nat -> eq nat n (nat_pred x)) (eq_refl nat n)
    ;;
    let double_injective : n:nat -> m:nat -> eq nat (double n) (double m) -> eq nat n m =
      fix F (n:nat) : (m:nat -> eq nat (double n) (double m) -> eq nat n m) ->
        match n as n in nat return m:nat -> eq nat (double n) (double m) -> eq nat n m with
        | O -> (
            fun m:nat ->
              match m as m in nat return eq nat (double O) (double m) -> eq nat O m with
              | O -> fun (e:eq nat (double O) (double O)) -> eq_refl nat O
              | S m' -> fun (e:eq nat (double O) (double (S m'))) ->
                  (* e: eq nat O (S (S (double m'))) *)
                  False_ind (eq nat O (S m')) (neq_nat_lemma (S (double m')) e) )
        | S n' ->
            fun m:nat ->
              match m as m in nat
                      return eq nat (double (S n')) (double m) -> eq nat (S n') m
              with
              | O -> fun e:eq nat (double (S n')) (double O) ->
                  (* e:eq nat (S (S (double n'))) O *)
                  False_ind (eq nat (S n') O) (neq_nat_lemma2 (S (double n')) e)
              | S m' -> fun e:eq nat (double (S n')) (double (S m')) ->
                  (* e:eq nat (S (S (double n'))) (S (S (double m'))) *)
                  f_apply nat nat
                          n' m'
                          (F n' m'
                             (S_injective (double n') (double m')
                                          (S_injective (S (double n')) (S (double m')) e)))
                          S
    ;;
"

test_positive "
    let and_intro : A:Univ 0 -> B:Univ 0 -> A -> B -> prod A B =
      fun (A:Univ 0) (B:Univ 0) (a:A) (b:B) -> pair A B a b
    ;;
    let and_example : n:nat -> m:nat -> prod (eq nat n O) (eq nat m O) -> eq nat (add n m) O =
      fun (n:nat) (m:nat) (p:prod (eq nat n O) (eq nat m O)) ->
        eq_trans nat
                 (add n m)
                 (add O m) (f_apply nat nat n O (prod_fst (eq nat n O) (eq nat m O) p) (fun k:nat -> add k m))
                 O         (prod_snd (eq nat n O) (eq nat m O) p)
    ;;
"

test_positive "
    let zero_or_succ : n:nat -> either (eq nat n O) (eq nat n (S (nat_pred n))) =
      fun n:nat ->
        match n as n in nat return either (eq nat n O) (eq nat n (S (nat_pred n))) with
        | O -> left (eq nat O O) (eq nat O (S (nat_pred O))) (eq_refl nat O)
        | S n' -> right (eq nat (S n') O) (eq nat (S n') (S (nat_pred (S n')))) (eq_refl nat (S n'))
    ;;
"

#test_positive "
#    let not : P:Univ 0 -> Univ 0 = fun P:Univ 0 -> (P -> False);;
#    let not_False : not False = fun P:False -> P;;
#    let contradiction_implies_anything : P:Univ 0 -> Q:Univ 0 -> prod P (not P) -> Q =
#      fun (P:Univ 0) (Q:Univ 0) (p:prod P (not P)) ->
#        False_ind Q ((prod_snd P (not P) p) (prod_fst P (not P) p))
#    ;;
#"

function test_negative() {
    res=$(echo "$1" | $QLOWN 2>&1)
    if ( echo "$res" | grep -i "error" > /dev/null ); then
        :
    else
        echo "$res"
        fail "$1"
    fi
}

test_negative "
    let f : P:Univ 0 -> P -> P -> P =
      fun P:Univ 0 -> fun x:P -> x;;
"

test_negative "
    let f : P:Univ 0 -> Q:Univ 0 -> P -> Q -> P =
      fun P:Univ 0 -> fun Q:Univ 0 -> fun x:Q -> fun y:P -> x;;
"

test_negative "
    let f : P:Univ 0 -> P -> (P -> False) -> False =
      fun P:Univ 0 -> fun x:P -> fun y:(P -> False) -> x y;;
"

test_negative "
    let f : A:Univ 0 -> x:A -> y:A -> z:A ->
            eq A x y -> eq A y z -> eq A x z =
      fun A:Univ 0 -> fun x:A -> fun y:A -> fun z:A ->
      fun e1:eq A x y -> fun e2:eq A y z ->
        eq_subst A y z e1 (fun w:A -> eq A x w) e1;;
"

test_negative "
    let f_apply : A:Univ 10 -> B:Univ 10 -> x:A -> y:A -> eq A x y ->
                  f:(A -> B) -> eq B (f x) (f y) =
      fun A:Univ 10 -> fun B:Univ 10 -> fun x:A -> fun y:A -> fun e:eq A x y ->
      fun f:(A -> B) ->
        match e as _ in eq A x y return eq B (f x) (f y) with
        | eq_refl A x -> eq_refl B (f x)
    ;;
"

test_negative "
    type natprod : Univ 0 =
    | pair : nat -> nat -> natprod
    ;;
    let fst : natprod -> nat =
      fun p:natprod ->
        match p as _ in natprod return nat with
        | pair x _ -> x
    ;;
    let snd : natprod -> nat =
      fun p:natprod ->
        match p as _ in natprod return nat with
        | pair _ y -> y
    ;;
    let surjective_pairing : n:nat -> m:nat ->
                             eq natprod (pair n m)
                                        (pair (fst (pair n m)) (snd (pair n n))) =
      fun n:nat -> fun m:nat -> eq_refl natprod (pair n m)
    ;;
"
