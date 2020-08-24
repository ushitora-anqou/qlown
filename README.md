# Qlown

Yet another toy theorem verifier strongly inspired by [this article](https://qiita.com/kikx/items/10d143edc090bdfec477).

## Build and Run

```
$ dune build
$ _build/default/qlown.exe
# let f : P:Univ 0 -> Q:Univ 0 -> P -> Q -> P =
    fun P:Univ 0 -> fun Q:Univ 0 -> fun x:P -> fun y:Q -> x;;
f added (VERIFIED)
# let f : P:Univ 0 -> Q:Univ 0 -> P -> Q -> P =
    fun P:Univ 0 -> fun Q:Univ 0 -> fun x:P -> fun y:Q -> y;;
Error: Failure("type check failed")
# (* Prove \forall n, m \in Nat, n + m = m + n. Lemmas are in stdlib.qlown. *)
let nat_comm : n:nat -> m:nat -> eq nat (add n m) (add m n) =
  nat_rect (fun n:nat -> m:nat -> eq nat (add n m) (add m n))
           (fun m:nat -> eq_trans nat (add O m) m (add m O) (eq_refl nat m) (eq_sym nat (add m O) m (nat_plus_n_O m)))
           (fun n:nat -> fun H:(m:nat -> eq nat (add n m) (add m n)) -> fun m:nat ->
             eq_trans nat (add (S n) m) (S (add n m)) (add m (S n))
                          (eq_refl nat (add (S n) m))
                          (eq_trans nat (S (add n m)) (S (add m n)) (add m (S n))
                                        (f_apply nat nat (add n m) (add m n) S (H m))
                                        (nat_plus_n_Sm m n)))
;;
nat_comm added (VERIFIED)
```

## Thanks to

["Write Yourself a Theorem Prover in 48 Hours"](https://qiita.com/kikx/items/10d143edc090bdfec477).
