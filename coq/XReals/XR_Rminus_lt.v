Require Export XR_Rminus.
Require Export XR_Rplus_lt_reg_r.

Local Open Scope R_scope.

Lemma Rminus_lt : forall r1 r2,
  r1 - r2 < R0 ->
  r1 < r2.
Proof.
  intros x y h.
  apply Rplus_lt_reg_r with (-y).
  rewrite Rplus_opp_r.
  unfold Rminus in h.
  exact h.
Qed.