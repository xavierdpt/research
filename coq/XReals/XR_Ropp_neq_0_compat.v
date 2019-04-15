Require Export XR_R.
Require Export XR_Ropp.
Require Export XR_Rplus_0_l.
Require Export XR_Rplus_opp_r.
Require Export XR_Rplus_eq_reg_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Ropp_neq_0_compat : forall r, r <> R0 -> - r <> R0.
Proof.
  intros x h.
  unfold not.
  unfold not in h.
  intro heq.
  apply h.
  apply Rplus_eq_reg_r with (-x).
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  symmetry.
  exact heq.
Qed.
