Require Export XR_Ropp_minus_distr.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_minus_distr' : forall r1 r2, - (r2 - r1) = r1 - r2.
Proof.
  intros x y.
  apply Ropp_minus_distr.
Qed.