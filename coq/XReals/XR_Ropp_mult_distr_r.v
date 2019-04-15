Require Export XR_Ropp_mult_distr_l.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_mult_distr_r : forall r1 r2, - (r1 * r2) = r1 * - r2.
Proof.
  intros x y.
  rewrite Rmult_comm.
  rewrite Ropp_mult_distr_l.
  rewrite Rmult_comm.
  reflexivity.
Qed.
