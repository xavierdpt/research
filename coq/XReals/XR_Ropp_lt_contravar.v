Require Export XR_Rplus_lt_reg_r.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.

Lemma Ropp_lt_contravar : forall r1 r2,
  r2 < r1 ->
  - r1 < - r2.
Proof.
  intros x y.
  intros h.
  apply Rplus_lt_reg_r with y.
  rewrite Rplus_opp_l.
  apply Rplus_lt_reg_l with x.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  rewrite Rplus_0_r.
  exact h.
Qed.