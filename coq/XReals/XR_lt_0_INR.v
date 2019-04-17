Require Export Arith.
Require Export XR_S_INR.
Require Export XR_Rlt_trans.
Require Export XR_Rlt_plus_1.

Local Open Scope R_scope.

Lemma lt_0_INR : forall n:nat,
  (0 < n)%nat ->
  R0 < INR n.
Proof.
  intros n hn.
  induction n as [ | n hin ].
  { inversion hn. }
  {
    unfold lt in hn.
    inversion hn as [ eq | n' hn' ].
    {
      subst n.
      simpl.
      exact Rlt_0_1.
    }
    {
      subst n'.
      rewrite S_INR.
      apply Rlt_trans with (INR n).
      {
        apply hin.
        apply lt_le_trans with 1%nat.
        {
          unfold lt.
          apply le_n.
        }
        { exact hn'. }
      }
      { apply Rlt_plus_1. }
    }
  }
Qed.

