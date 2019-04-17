Require Export XR_Rlt_0_1.

Local Open Scope R_scope.

Lemma Rle_0_1 : R0 <= R1.
Proof.
  unfold "<=".
  left.
  exact Rlt_0_1.
Qed.
