Require Export XR_eq_IZR_R0.
Require Export XR_minus_IZR.

Local Open Scope R_scope.

Lemma eq_IZR : forall n m:Z, IZR n = IZR m -> n = m.
Proof.
  intros n m h.
  Search ( _ - _ = _ -> _ = _)%Z.
  apply Zminus_eq.
  apply eq_IZR_R0.
  rewrite minus_IZR.
  unfold Rminus.
  apply Rplus_eq_reg_r with (IZR m).
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite Rplus_0_l.
  exact h.
Qed.
