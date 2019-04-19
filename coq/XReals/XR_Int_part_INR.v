Require Export XR_Int_part.
Require Export XR_tech_up.
Require Export XR_INR_IZR_INZ.
Require Export XR_Rle_refl.

Local Open Scope R_scope.

Lemma Int_part_INR : forall n:nat,
  Int_part (INR n) = Z.of_nat n.
Proof.
  intro n.
  unfold Int_part.
  symmetry.
  apply Zplus_minus_eq.
  symmetry.
  apply tech_up.
  {
    rewrite plus_IZR.
    rewrite <- INR_IZR_INZ.
    rewrite Rplus_comm.
    pattern (INR n) at 1 ; rewrite <- Rplus_0_r.
    apply Rplus_lt_compat_l.
    simpl.
    exact Rlt_0_1.
  }
  {
    rewrite plus_IZR.
    rewrite <- INR_IZR_INZ.
    rewrite Rplus_comm.
    simpl.
    apply Rle_refl.
  }
Qed.