Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rle.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof.
  intros x y h.
  unfold "<=".
  left.
  exact h.
Qed.
