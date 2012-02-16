Require Import List.
Require Import Arith.
Require Import Recdef.

Lemma fil_len : forall (l:list nat) (p:nat->bool),
  length (filter p l) <= length l.
intros.
induction l.
unfold length.
auto.
simpl.
case (p a).
simpl.
apply le_n_S.
apply IHl.
auto.
Qed.


Function qsort (l : list nat) {measure length l} : list nat :=
  match l with
  | nil => nil
  | x :: xs => qsort (filter (leb x) xs)
                 ++ (x ::nil)++ qsort (filter (fun t=>negb(leb x t)) xs)
  end.

intros.
simpl.
apply le_n_S.
apply fil_len.
intros.
simpl.
apply le_n_S.
apply fil_len.
Defined.

Extraction Language Haskell.
Extraction "qst.hs" qsort.
(*
Fixpoint qsort (l:list nat):list nat:=
 match l with
 | nil => nil
 | x::xs => qsort (filter (leb x) xs) ++
            (x::nil)++
            qsort (filter (fun t=>negb(leb x t)) xs)
 end.
*)