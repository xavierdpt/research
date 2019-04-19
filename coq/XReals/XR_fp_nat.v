Require Export XR_frac_part.
Require Export XR_Rplus_eq_reg_r.

Local Open Scope R_scope.

Lemma fp_nat : forall r:R,
  frac_part r = R0 ->
  exists c : Z, r = IZR c.
Proof.
  intros x h.
  unfold frac_part in h.
  unfold Int_part in h.
  exists (up x - 1)%Z.
  unfold Rminus in h.
  apply Rplus_eq_reg_r with (- (IZR (up x - 1))).
  rewrite Rplus_opp_r.
  exact h.
Qed.
