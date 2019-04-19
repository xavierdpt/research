Require Export XR_frac_part.
Require Export XR_archimed.
Require Export XR_minus_IZR.
Require Export XR_Ropp_le_cancel.
Require Export XR_Rplus_le_reg_r.
Require Export XR_Rplus_lt_compat_r.

Local Open Scope R_scope.

Lemma base_fp : forall r:R, R0 <= frac_part r /\ frac_part r < R1.
Proof.
  intro x.
  destruct (archimed x) as [ hl hu ].
  unfold frac_part.
  unfold Int_part.
  rewrite minus_IZR.
  simpl.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite <- Rplus_assoc.
  split.
  {
    apply Ropp_le_cancel.
    repeat rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    apply Rplus_le_reg_r with R1.
    rewrite Ropp_0.
    rewrite Rplus_0_l.
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_l, Rplus_0_r.
    rewrite Rplus_comm.
    unfold Rminus in hu.
    exact hu.
  }
  {
    pattern R1 at 2 ; rewrite <- Rplus_0_l.
    apply Rplus_lt_compat_r.
    eapply Rplus_lt_reg_r.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l, Rplus_0_r, Rplus_0_l.
    exact hl.
  }
Qed.
