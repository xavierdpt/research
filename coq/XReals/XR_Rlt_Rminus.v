Require Export XR_Rminus.
Require Export XR_Rplus_lt_reg_r.
Require Export XR_Rplus_0_r.

Local Open Scope R_scope.

Lemma Rlt_Rminus : forall a b:R,
  a < b ->
  R0 < b - a.
Proof.
  intros x y h.
  unfold Rminus.
  apply Rplus_lt_reg_r with x.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_0_r.
  exact h.
Qed.
