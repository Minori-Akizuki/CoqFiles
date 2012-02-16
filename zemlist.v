Require Import List.
Theorem app_zero :
 forall (A:Type)(l:list A), l++nil=l.
intros.
induction l.
simpl.
reflexivity.
simpl.
apply (f_equal (cons a)).
apply IHl.
Qed.

Goal forall (n:nat),n+0=n.
intros.
induction n.
reflexivity.
simpl.
f_equal.
apply IHn.
Qed.