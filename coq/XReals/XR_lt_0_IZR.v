Require Export XR_IZR.
Require Export XR_INR_lt.
Require Export XR_Ropp_lt_cancel.

Local Open Scope R_scope.

Lemma lt_0_IZR : forall n:Z, R0 < IZR n -> (0 < n)%Z.
Proof.
  intro n.
  destruct n as [ | n | n ].
  {
    simpl.
    intro h.
    apply Rlt_irrefl in h.
    contradiction.
  }
  {
    simpl.
    intros _.
    apply Pos2Z.is_pos.
  }
  {
    simpl.
    intro h.
    rewrite <- Ropp_0 in h.
    apply Ropp_lt_cancel in h.
    exfalso.
    eapply Rlt_irrefl.
    eapply Rlt_trans.
    { apply h. }
    {
      change R0 with (INR 0).
      apply lt_INR.
      apply Pos2Nat.is_pos.
    }
  }
Qed.