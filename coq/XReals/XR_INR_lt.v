Require Export Arith.
Require Export XR_lt_INR.

Local Open Scope R_scope.

Lemma INR_lt : forall n m:nat,
  INR n < INR m ->
  (n < m)%nat.
Proof.
  intros n.
  induction n as [ | n hn ].
  {
    intros m hm.
    destruct m as [ | m ].
    {
      exfalso.
      apply Rlt_irrefl in hm.
      contradiction.
    }
    {
      unfold lt.
      apply le_n_S.
      apply le_O_n.
    }
  }
  {
    intros m hnm.
    destruct m as [ | m ].
    {
      exfalso.
      clear hn.
      apply Rlt_irrefl with R0.
      apply Rlt_trans with (INR (S n)).
      {
        replace R0 with (INR 0%nat).
        {
          apply lt_INR.
          unfold lt.
          apply le_n_S.
          apply le_O_n.
        }
        {
          simpl.
          reflexivity.
        }
      }
      {
        simpl in hnm.
        exact hnm.
      }
    }
    {
      apply lt_n_S.
      apply hn.
      apply Rplus_lt_reg_r with R1.
      rewrite <- S_INR.
      rewrite <- S_INR.
      exact hnm.
    }
  }
Qed.