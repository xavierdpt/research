Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rtotal_order.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_or_le : forall r1 r2, r1 < r2 \/ r2 <= r1.
Proof.
intros x y.
destruct (Rtotal_order x y) as [ hxy | [ heq | hyx ] ].
{ left. exact hxy. }
{ subst y. right. unfold "<=". right. reflexivity. }
{ right. unfold "<=". left. exact hyx. }
Qed.
