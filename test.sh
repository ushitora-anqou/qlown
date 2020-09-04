#!/bin/bash

dune build
QLOWN=_build/default/qlown.exe

function fail() {
    echo -ne "\e[1;31m[ERROR]\e[0m "
    echo "$1"
    exit 1
}

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
