Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rtotal_order.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_or_lt : forall r1 r2, r1 <= r2 \/ r2 < r1.
Proof.
intros x y.
destruct (Rtotal_order x y) as [ hxy | [ heq | hyx ] ].
{ left. unfold "<=". left. exact hxy. }
{ subst y. left. unfold "<=". right. reflexivity. }
{ right. exact hyx. }
Qed.
