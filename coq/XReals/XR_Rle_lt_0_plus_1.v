Require Export XR_Rlt_0_1.
Require Export XR_Rplus_le_lt_compat.

Local Open Scope R_scope.

Lemma Rle_lt_0_plus_1 : forall r,
  R0 <= r ->
  R0 < r + R1.
Proof.
  intros x h.
  rewrite <- Rplus_0_l with R0.
  apply Rplus_le_lt_compat.
  { exact h. }
  { exact Rlt_0_1. }
Qed.