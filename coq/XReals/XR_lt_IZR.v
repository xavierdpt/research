Require Export XR_lt_0_IZR.
Require Export XR_minus_IZR.

Local Open Scope R_scope.

Lemma lt_IZR : forall n m:Z, IZR n < IZR m -> (n < m)%Z.
Proof.
  intros n m h.
  apply Z.lt_0_sub.
  apply lt_0_IZR.
  rewrite minus_IZR.
  apply Rplus_lt_reg_r with (IZR n).
  rewrite Rplus_0_l.
  unfold Rminus.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  exact h.
Qed.