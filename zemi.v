Goal forall (P Q:Prop), P/\Q->Q/\P.
intros.
case H.
intros.
apply conj.
apply H1.
apply H0.
Qed.


Goal forall (P Q:Prop), ~P\/~Q -> ~(P/\Q).
intros.
intro.
case H0.
intros.
case H.
intro.
apply H3.
apply H1.
intro.
apply H3.
apply H2.
Qed.

Goal forall (A B C:Prop), (B->C)->(A->B)->(A->C).
intros.
apply H.
apply H0.
apply H1.
Qed.

Definition nnP :forall (A:Prop), A -> ~~A.
unfold not.
intros.
apply H0.
apply H.
Qed.

Goal forall (A:Prop), A\/~A -> ~~A -> A.
unfold not.
intros.
destruct H.
apply H.
apply False_ind.
apply H0.
apply H.
Qed.

Definition ththm : forall (A B C:Prop),
 (B->C)->(A->B)->(A->C) :=
 fun A B C f g x => f (g x).