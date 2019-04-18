Require Export XR_R2.
Require Export XR_Rplus_lt_compat.
Require Export XR_Rlt_0_1.

Local Open Scope R_scope.

Lemma R2_neq_R0 : R2 <> R0.
Proof.
  unfold not.
  intro eq.
  apply Rlt_irrefl with R0.
  pattern R0 at 2 ; rewrite <- eq.
  unfold R2.
  rewrite <- Rplus_0_l with R0.
  apply Rplus_lt_compat.
  { exact Rlt_0_1. }
  { exact Rlt_0_1. }
Qed.