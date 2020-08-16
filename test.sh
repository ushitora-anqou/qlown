#!/bin/bash

dune build
QLOWN=_build/default/qlown.exe

function fail() {
    echo -ne "\e[1;31m[ERROR]\e[0m "
    echo "$1"
    exit 1
}

function test_positive() {
    res=$(echo "$1" | $QLOWN)
    if ( echo "$res" | grep "Error" > /dev/null ); then
        echo "$res"
        fail "$1"
    fi
}

test_positive "
    let False : Univ 0;;
    let False_ind : (P : Univ 0) -> False -> P;;

    let f : (P : Univ 0) -> P -> P =
       fun (P : Univ 0) -> fun (x : P) -> x;;
    let f : (P : Univ 0) -> (Q : Univ 0) -> P -> Q -> P =
       fun (P : Univ 0) -> fun (Q : Univ 0) -> fun (x : P) -> fun (y : Q) -> x;;
    let f : (P : Univ 0) -> False -> P = False_ind;;
    let f : (P : Univ 0) -> P -> (P -> False) -> False =
       fun (P : Univ 0) -> fun (x : P) -> fun (y : P -> False) -> y x;;
"

function test_negative() {
    res=$(echo "$1" | $QLOWN)
    if ( echo "$res" | grep " VERIFIED" > /dev/null ); then
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
test_negative "
    let False : Univ 0;;
    let False_ind : (P : Univ 0) -> False -> P;;
    let f : (P : Univ 0) -> False -> P = False;;
"
test_negative \
    "let f : (P : Univ 0) -> P -> (P -> False) -> False =
       fun (P : Univ 0) -> fun (x : P) -> fun (y : P -> False) -> x y;;"
