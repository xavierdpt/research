Require Export XR_not_0_IZR.
Require Export XR_lt_IZR.

Local Open Scope R_scope.

Lemma le_0_IZR : forall n:Z, R0 <= IZR n -> (0 <= n)%Z.
Proof.
  intros n h.
  unfold "<=" in h.
  destruct h as [ h | heq ].
  {
    apply Z.lt_le_incl.
    apply lt_IZR.
    simpl.
    exact h.
  }
  {
    apply Z.eq_le_incl.
    apply eq_IZR.
    simpl.
    exact heq.
  }
Qed.
