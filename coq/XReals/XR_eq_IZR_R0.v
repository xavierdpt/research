Require Export XR_IZR.
Require Export XR_lt_INR.

Local Open Scope R_scope.

Lemma eq_IZR_R0 : forall n:Z, IZR n = R0 -> n = 0%Z.
Proof.
  intro n.
  destruct n as [ | n | n ].
  {
    intros _.
    reflexivity.
  }
  {
    simpl.
    intro h.
    exfalso.
    eapply Rlt_irrefl with R0.
    pattern R0 at 2 ; rewrite <- h.
    change R0 with (INR 0).
    apply lt_INR.
    apply Pos2Nat.is_pos.
  }
  {
    simpl.
    intro h.
    exfalso.
    apply Rlt_irrefl with (-R0).
    pattern R0 at 2 ; rewrite <- h.
    rewrite Ropp_involutive.
    rewrite Ropp_0.
    change R0 with (INR 0).
    apply lt_INR.
    apply Pos2Nat.is_pos.
  }
Qed.