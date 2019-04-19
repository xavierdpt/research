Require Export XR_frac_part.
Require Export XR_Ropp_eq_compat.
Require Export XR_IZR_eq.
Require Export XR_tech_up.
Require Export XR_Rle_refl.

Local Open Scope R_scope.

Lemma fp_R0 : frac_part R0 = R0.
Proof.
  unfold frac_part.
  unfold Rminus.
  rewrite Rplus_0_l.
  pattern R0 at 2 ; rewrite <- Ropp_0.
  apply Ropp_eq_compat.
  change R0 at 2 with (IZR 0).
  apply IZR_eq.
  unfold Int_part.
  apply Zeq_minus.
  symmetry.
  apply tech_up.
  {
    simpl.
    exact Rlt_0_1.
  }
  {
    simpl.
    rewrite Rplus_0_l.
    apply Rle_refl.
  }
Qed.
