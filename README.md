# Qlown

Yet another toy theorem prover strongly inspired by [this article](https://qiita.com/kikx/items/10d143edc090bdfec477).

## Build and Run

```
$ dune build
$ _build/default/qlown.exe
# let f : (P : Univ 0) -> (Q : Univ 0) -> P -> (Q -> P) =
    fun (P : Univ 0) -> fun (Q : Univ 0) -> fun (x : P) -> fun (y : Q) -> x;;
f VERIFIED
# let f : (P : Univ 0) -> (Q : Univ 0) -> P -> (Q -> P) =
    fun (P : Univ 0) -> fun (Q : Univ 0) -> fun (x : P) -> fun (y : Q) -> y;;
f UNVERIFIED
```

## Thanks to

["Write Yourself a Theorem Prover in 48 Hours"](https://qiita.com/kikx/items/10d143edc090bdfec477).
