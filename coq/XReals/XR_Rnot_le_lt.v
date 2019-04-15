Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rtotal_order.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rnot_le_lt : forall r1 r2, ~ r1 <= r2 -> r2 < r1.
Proof.
  intros x y.
  unfold not.
  unfold "<=".
  intro h.
  destruct (Rtotal_order x y) as [ hxy | [ heq | hyx ] ].
  {
    exfalso.
    apply h.
    left.
    exact hxy.
  }
  {
    exfalso.
    apply h.
    right.
    exact heq.
  }
  { exact hyx. }
Qed.
