Require Export XR_R2_neq_R0.

Local Open Scope R_scope.

Lemma Rlt_R0_R2 : R0 < R2.
Proof.
  unfold R2.
  rewrite <- Rplus_0_r with R0.
  apply Rplus_lt_compat.
  exact Rlt_0_1.
  exact Rlt_0_1.
Qed.