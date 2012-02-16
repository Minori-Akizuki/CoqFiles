Require Import Arith.
Definition kk : forall (n:nat),
 (exists m : nat, n = m * 4)
  -> exists k : nat, n = k * 2.
intros.
destruct H.
exists (x*2).
rewrite mult_assoc_reverse.
simpl.
apply H.
Qed.

