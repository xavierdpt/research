Require Export XR_Rle.
Require Export XR_Rminus_lt.
Require Export XR_Rminus_diag_uniq.

Local Open Scope R_scope.

Lemma Rminus_le : forall r1 r2,
  r1 - r2 <= R0 ->
  r1 <= r2.
Proof.
  intros x y h.
  unfold "<=" in h.
  destruct h as [ h | heq ].
  {
    unfold "<=".
    left.
    apply Rminus_lt.
    exact h.
  }
  {
    unfold "<=".
    right.
    apply Rminus_diag_uniq.
    exact heq.
  }
Qed.