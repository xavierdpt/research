Require Export XR_le_0_IZR.
Require Export XR_minus_IZR.
Require Export XR_Rplus_le_reg_r.

Local Open Scope R_scope.

Lemma le_IZR : forall n m:Z, IZR n <= IZR m -> (n <= m)%Z.
Proof.
  intros n m h.
  apply Zle_0_minus_le.
  apply le_0_IZR.
  rewrite minus_IZR.
  unfold Rminus.
  apply Rplus_le_reg_r with (IZR n).
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite Rplus_0_l.
  exact h.
Qed.