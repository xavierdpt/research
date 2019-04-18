Require Export XR_plus_IZR_NEG_POS.

Local Open Scope R_scope.

Arguments Z.add _ _ : simpl nomatch.

Lemma plus_IZR : forall n m:Z, IZR (n + m) = IZR n + IZR m.
Proof.
  intros n.
  destruct n as [ | n | n ].
  {
    intro m.
    simpl.
    rewrite Rplus_0_l.
    reflexivity.
  }
  {
    intro m.
    simpl.
    destruct m as [ | m | m ].
    {
      simpl.
      rewrite Rplus_0_r.
      reflexivity.
    }
    {
      simpl.
      rewrite Pos2Nat.inj_add.
      rewrite plus_INR.
      reflexivity.
    }
    {
      rewrite plus_IZR_NEG_POS.
      simpl.
      reflexivity.
    }
  }
  {
    simpl.
    intro m.
    destruct m.
    {
      simpl.
      rewrite Rplus_0_r.
      reflexivity.
    }
    {
      rewrite Z.add_comm.
      rewrite plus_IZR_NEG_POS.
      simpl.
      rewrite Rplus_comm.
      reflexivity.
    }
    {
      simpl.
      rewrite Pos2Nat.inj_add.
      rewrite plus_INR.
      rewrite Ropp_plus_distr.
      reflexivity.
    }
  }
Qed.



