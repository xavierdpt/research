Require Export XR_Int_part.
Require Export XR_minus_IZR.
Require Export XR_archimed.
Require Export XR_Ropp_le_cancel.
Require Export XR_Rplus_le_reg_l.
Require Export XR_Rplus_lt_compat_r.

Local Open Scope R_scope.

Lemma base_Int_part : forall r,
  IZR (Int_part r) <= r /\ - R1 < IZR (Int_part r) - r .
Proof.
  intro x.
  unfold Int_part.
  rewrite minus_IZR.
  simpl.
  destruct (archimed x) as [ hl hu ].
  unfold Rminus.
  unfold Rminus in hu.
  split.
  {
    apply Ropp_le_cancel.
    rewrite Ropp_plus_distr, Ropp_involutive.
    eapply Rplus_le_reg_l with (IZR (up x)).
    repeat rewrite <- Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_l.
    exact hu.
  }
  {
    pattern (-R1) at 1 ; rewrite <- Rplus_0_l.
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm (-R1)).
    repeat rewrite <- Rplus_assoc.
    apply Rplus_lt_compat_r.
    apply Rplus_lt_reg_r with x.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l, Rplus_0_r, Rplus_0_l.
    exact hl.
  }
Qed.
