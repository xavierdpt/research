Require Export XR_R1_neq_R0.
Require Export XR_Rinv_r.
Require Export XR_Rmult_eq_reg_l.
Require Export XR_Rmult_eq_reg_r.
Require Export XR_Rmult_0_l.

Local Open Scope R_scope.

Lemma Rinv_neq_0_compat : forall r, r <> R0 -> / r <> R0.
Proof.
  intros x hneq.
  unfold not.
  intro heq.
  apply hneq.
  pattern x ; rewrite <- Rmult_1_l.
  rewrite <- Rinv_l with x.
  {
    rewrite heq.
    rewrite Rmult_0_l.
    rewrite Rmult_0_l.
    reflexivity.
  }
  { exact hneq. }
Qed.
