Require Export XR_Rle_0_sqr.
Require Export XR_Rsqr_0_uniq.
Require Export XR_Rplus_eq_0_l.

Local Open Scope R_scope.

Lemma Rplus_sqr_eq_0_l : forall r1 r2,
  Rsqr r1 + Rsqr r2 = R0 ->
  r1 = R0.
Proof.
  intros x y h.
  apply Rsqr_0_uniq.
  apply Rplus_eq_0_l with (Rsqr y).
  { apply Rle_0_sqr. }
  { apply Rle_0_sqr. }
  { exact h. }
Qed.