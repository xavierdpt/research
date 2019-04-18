Require Export XR_Rdiv.
Require Export XR_Rmult_lt_0_compat.
Require Export XR_Rinv_0_lt_compat.

Local Open Scope R_scope.

Lemma Rdiv_lt_0_compat : forall a b,
  R0 < a ->
  R0 < b ->
  R0 < a / b.
Proof.
  intros x y hx hy.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  { exact hx. }
  {
    apply Rinv_0_lt_compat.
    exact hy.
  }
Qed.