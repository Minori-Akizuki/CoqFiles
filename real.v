Require Import Reals.
Open Scope R_scope.

Lemma sqGt01 : forall (r:R), r>0 -> r*r>0.
intros.
cut (r>0).
cut (r>0).
cut (0=0*r).
intro.
rewrite H0 at 3.
apply Rmult_gt_compat_r.
rewrite Rmult_0_l.
reflexivity.
apply H.
apply H.
Qed.

Lemma sqGt02 : forall (r:R), r=0 -> r*r=0.
intros.
rewrite H.
rewrite Rmult_0_r.
reflexivity.
Qed.

Lemma sqgt03 : forall (r:R), r<0 -> r*r>0.
intros.
cut (r<0).
cut (r<0).
cut (0=r*0).
intro.
rewrite H0 at 3.
apply Rmult_lt_gt_compat_neg_l.
rewrite Rmult_0_r.
reflexivity.
apply H.
apply H.
Qed.



Lemma sqrtGt0 : forall (x:R), x*x>=0.
intros.
cut (x<0\/x=0\/x>0).
intros.
case H.
intro.
cut (x*x>0).
apply Rgt_ge.
cut (x<0).
apply sqgt03.
apply H0.
intros.
case H0.
intros.
cut (x*x=0).
apply Req_ge.
rewrite H1.
rewrite Rmult_0_r.
reflexivity.
intro.
cut (x*x>0).
apply Rgt_ge.
cut (x>0).
apply sqGt01.
apply H1.
apply Rtotal_order.
Qed.


Lemma rsq0 : forall (r:R),r*r=0->r=0.
intros.
cut (r=0\/r=0).
intros.
case H0.
intro.
apply H1.
intro.
apply H1.
cut (r*r=0).
apply Rmult_integral.
apply H.
Qed.

Lemma add_gh_zero : forall (x y:R), 0<x /\ 0<=y -> 0<x+y.
intros.
case H.
intros.
case H1.
intros.
cut (forall (r1 r2:R),0<r1/\0<r2->0<r1+r2).
intros.
apply H3.
split.
apply H0.
apply H2.
intros.
case H3.
intros.
cut (r1<r1+r2).
cut (0<r1).
apply Rlt_trans.
apply H4.
cut (r1=r1+0).
intros.
rewrite H6 at 1.
cut (0<r2).
apply Rplus_lt_compat_l.
apply H5.
rewrite Rplus_0_r.
reflexivity .
intro.
cut (y=0).
intro.
rewrite H3.
rewrite Rplus_0_r.
apply H0.
rewrite H2.
reflexivity.

Goal forall (x y:R),x*x+y*y=0 -> x=0/\y=0.
intros.
split.
cut (~~(x=0)).
apply (Classical_Prop.NNPP).
unfold not at 1.
intros.
apply H0.




