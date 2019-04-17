Require Export XR_Rminus.
Require Export XR_Rplus_lt_reg_r.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.

Lemma Rlt_minus : forall r1 r2,
  r1 < r2 ->
  r1 - r2 < R0.
Proof.
  intros x y h.
  unfold Rminus.
  apply Rplus_lt_reg_r with y.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_0_r.
  exact h.
Qed.
