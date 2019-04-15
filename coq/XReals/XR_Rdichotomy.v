Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rtotal_order.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rdichotomy : forall r1 r2, r1 <> r2 -> r1 < r2 \/ r2 < r1.
Proof.
  intros x y.
  unfold not.
  intro hneq.
  destruct (Rtotal_order x y) as [ hxy | [ heq | hxy ] ].
  { left. exact hxy. }
  {
    specialize (hneq heq).
    contradiction.
  }
  { right. exact hxy. }
Qed.
