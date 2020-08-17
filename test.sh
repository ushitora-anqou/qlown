#!/bin/bash

dune build
QLOWN=_build/default/qlown.exe

function fail() {
    echo -ne "\e[1;31m[ERROR]\e[0m "
    echo "$1"
    exit 1
}

function test_positive() {
    res=$(echo "$1" | $QLOWN 2>&1)
    if ( echo "$res" | grep -i "error" > /dev/null ); then
        echo "$res"
        fail "$1"
    fi
}

test_positive "
    let f : (P : Univ 0) -> P -> P =
      fun (P : Univ 0) -> fun (x : P) -> x;;
    let f : (P : Univ 0) -> (Q : Univ 0) -> P -> Q -> P =
      fun (P : Univ 0) -> fun (Q : Univ 0) -> fun (x : P) -> fun (y : Q) -> x;;
    let f : (P : Univ 0) -> False -> P = False_ind;;
    let f : (P : Univ 0) -> P -> (P -> False) -> False =
      fun (P : Univ 0) -> fun (x : P) -> fun (y : P -> False) -> y x;;
    let f : (A : Univ 0) -> (x : A) -> (y : A) -> eq A x y -> eq A y x =
      fun (A : Univ 0) -> fun (x : A) -> fun (y : A) -> fun (e : eq A x y) ->
        eq_rec A x (fun (z : A) -> eq A z x) (eq_refl A x) y e;;
    let f : (A : Univ 0) -> (x : A) -> (y : A) -> (z : A) ->
            eq A x y -> eq A y z -> eq A x z =
      fun (A : Univ 0) -> fun (x : A) -> fun (y : A) -> fun (z : A) ->
      fun (e1 : eq A x y) -> fun (e2 : eq A y z) ->
        eq_rec A y (fun (w : A) -> eq A x w) e1 z e2;;
    let f : eq (Univ 1) (Univ 0) (Univ 0) = eq_refl (Univ 1) (Univ 0);;
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

test_negative \
    "let f : (P : Univ 0) -> P -> P -> P =
       fun (P : Univ 0) -> fun (x : P) -> x;;"
test_negative \
    "let f : (P : Univ 0) -> (Q : Univ 0) -> P -> Q -> P =
       fun (P : Univ 0) -> fun (Q : Univ 0) -> fun (x : Q) -> fun (y : P) -> x;;"
test_negative \
    "let f : (P : Univ 0) -> False -> P = False;;"
test_negative \
    "let f : (P : Univ 0) -> P -> (P -> False) -> False =
       fun (P : Univ 0) -> fun (x : P) -> fun (y : P -> False) -> x y;;"
test_negative "
    let f : (A : Univ 0) -> (x : A) -> (y : A) -> (z : A) ->
            eq A x y -> eq A y z -> eq A x z =
      fun (A : Univ 0) -> fun (x : A) -> fun (y : A) -> fun (z : A) ->
      fun (e1 : eq A x y) -> fun (e2 : eq A y z) ->
        eq_rec A y (fun (w : A) -> eq A x w) e1 z e1;;
"
