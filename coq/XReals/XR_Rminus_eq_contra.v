Require Export XR_Rminus.
Require Export XR_Rplus_opp_r.
Require Export XR_Rplus_eq_reg_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rminus_eq_contra : forall r1 r2, r1 <> r2 -> r1 - r2 <> R0.
Proof.
  intros x y.
  intro hneq.
  unfold not.
  intro heq.
  unfold not in hneq.
  apply hneq.
  apply Rplus_eq_reg_r with (-y).
  rewrite Rplus_opp_r.
  unfold Rminus in heq.
  exact heq.
Qed.
