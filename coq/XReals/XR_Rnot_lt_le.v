Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rtotal_order.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rnot_lt_le : forall r1 r2, ~ r1 < r2 -> r2 <= r1.
Proof.
  intros x y.
  unfold "~".
  intro h.
  unfold "<=".
  destruct (Rtotal_order x y) as [ hxy | [ heq | hyx ] ].
  {
    exfalso.
    apply h.
    exact hxy.
  }
  {
    subst y.
    right.
    reflexivity.
  }
  {
    left.
    exact hyx.
  }
Qed.
