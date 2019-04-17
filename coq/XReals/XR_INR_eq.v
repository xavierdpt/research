Require Export XR_Rplus_le_lt_compat.
Require Export XR_pos_INR.

Local Open Scope R_scope.

Lemma INR_eq : forall n m:nat,
  INR n = INR m ->
  n = m.
Proof.
  intro n.
  induction n as [ | n hin ].
  {
    destruct m as [ | m ].
    {
      intros _.
      reflexivity.
    }
    {
      intro heq.
      simpl in heq.
      rewrite S_INR in heq.
      exfalso.
      apply Rlt_irrefl with R0.
      pattern R0 at 2 ; rewrite heq.
      rewrite <- Rplus_0_r with R0.
      apply Rplus_le_lt_compat.
      { apply pos_INR. }
      { exact Rlt_0_1. }
    }
  }
  {
    intros m hnm.
    destruct m as [ | m ].
    {
      simpl in hnm.
      exfalso.
      clear hin.
      rewrite S_INR in hnm.
      apply Rlt_irrefl with R0.
      pattern R0 at 2 ; rewrite <- hnm.
      clear hnm.
      rewrite <- Rplus_0_r with R0.
      apply Rplus_le_lt_compat.
      { apply pos_INR. }
      { exact Rlt_0_1. }
    }
    {
      apply eq_S.
      apply hin.
      apply Rplus_eq_reg_r with R1.
      rewrite <- S_INR.
      rewrite <- S_INR.
      exact hnm.
    }
  }
Qed.