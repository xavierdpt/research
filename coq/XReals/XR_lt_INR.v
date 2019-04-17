Require Export XR_lt_0_INR.
Require Export XR_Rplus_lt_compat_r.

Local Open Scope R_scope.

Lemma lt_INR : forall n m:nat,
  (n < m)%nat ->
  INR n < INR m.
Proof.
  intros n.
  induction n as [ | n hn ].
  {
    intros m hm.
    apply lt_0_INR.
    exact hm.
  }
  {
    intros m hsnm.
    destruct m as [ | m ].
    { inversion hsnm. }
    {
      rewrite S_INR.
      rewrite S_INR.
      apply Rplus_lt_compat_r.
      apply hn.
      apply lt_S_n.
      exact hsnm.
    }
  }
Qed.