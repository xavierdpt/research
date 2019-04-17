Require Export XR_Rlt_0_sqr.
Require Export XR_R1_neq_R0.

Local Open Scope R_scope.

Lemma Rlt_0_1 : R0 < R1.
Proof.
  rewrite <- Rmult_1_l with R1.
  fold (Rsqr R1).
  apply Rlt_0_sqr.
  exact R1_neq_R0.
Qed.