Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rtotal_order : forall r1 r2, r1 < r2 \/ r1 = r2 \/ r2 < r1.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ hxy | heq ] | hyx ].
  { left. exact hxy. }
  { right. left. exact heq. }
  { right. right. exact hyx. }
Qed.
