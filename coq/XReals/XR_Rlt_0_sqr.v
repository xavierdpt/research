Require Export XR_Rle_0_sqr.
Require Export XR_Rmult_integral.

Local Open Scope R_scope.

Lemma Rlt_0_sqr : forall r,
  r <> R0 ->
  R0 < Rsqr r.
Proof.
  intros x h .
  assert (hle := Rle_0_sqr x).
  unfold "<=" in hle.
  destruct hle as [ hlt | heq ].
  { exact hlt. }
  {
    exfalso.
    unfold Rsqr in heq.
    symmetry in heq.
    apply Rmult_integral in heq.
    destruct heq as [ heq | heq ].
    {
      subst x.
      unfold not in h.
      apply h.
      reflexivity.
    }
    {
      subst x.
      unfold not in h.
      apply h.
      reflexivity.
    }
  }
Qed.
