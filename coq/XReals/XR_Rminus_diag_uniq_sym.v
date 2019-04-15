Require Export XR_Rminus_diag_uniq.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rminus_diag_uniq_sym : forall r1 r2, r2 - r1 = R0 -> r1 = r2.
Proof.
  intros x y heq.
  symmetry.
  apply Rminus_diag_uniq.
  exact heq.
Qed.