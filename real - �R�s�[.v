Require Import Reals.
Open Scope R_scope.

Lemma sqrtGt0 : forall (x:R), x*x>=0.
intros.
cut (forall (r:R), r>=0 -> r*r>=0).
cut (forall (r:R), r=0 -> r*r=0).
cut (forall (r:R), r<=0 -> r*r>=0).
cut (x>=0\/x=0\/x<=0).
intros.
case H.
apply H2.
intro.
case H3.
intro.
rewrite H4.
cut (0*0=0).
apply Req_ge.
pattern (0*0).
rewrite Rmult_0_r.
reflexivity.
intros.


(*
cut (x=0\/x=0).
intro.
case H0.
intro.
apply H1.
intro.
apply H1.
apply Rmult_integral.
apply H.
Qed.
*)

Goal forall (x y:R),x*x+y*y=0 -> x=0/\y=0.
intros.
apply conj.
cut (x*x=0).
apply sqrtGt0.

