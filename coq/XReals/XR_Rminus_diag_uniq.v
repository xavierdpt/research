Require Export XR_Rminus.
Require Export XR_Rplus_opp_r.
Require Export XR_Rplus_eq_reg_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rminus_diag_uniq : forall r1 r2, r1 - r2 = R0 -> r1 = r2.
Proof.
  intros x y.
  intro heq.
  unfold Rminus in heq.
  apply Rplus_eq_reg_r with (-y).
  rewrite Rplus_opp_r.
  exact heq.
Qed.