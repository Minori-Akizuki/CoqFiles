Fact orsw : forall (A B:Prop), A\/B->B\/A.
intros.
case H.
intro.
apply or_intror.
apply H0.
intro.
apply or_introl.
apply H0.
Qed.