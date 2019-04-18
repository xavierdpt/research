Require Export XR_plus_IZR.
Require Export XR_mult_INR.
Require Export XR_Ropp_mult_distr_r.

Local Open Scope R_scope.

Lemma mult_IZR : forall n m:Z, IZR (n * m) = IZR n * IZR m.
Proof.
  intro n.
  destruct n as [ | n | n ].
  {
    intro m.
    simpl.
    rewrite Rmult_0_l.
    reflexivity.
  }
  {
    intro m.
    destruct m as [ | m | m ].
    {
      simpl.
      rewrite Rmult_0_r.
      reflexivity.
    }
    {
      simpl.
      rewrite Pos2Nat.inj_mul.
      rewrite mult_INR.
      reflexivity.
    }
    {
      simpl.
      rewrite Pos2Nat.inj_mul.
      rewrite mult_INR.
      rewrite <- Ropp_mult_distr_r.
      reflexivity.
    }
  }
  {
    intro m.
    destruct m as [ | m | m ].
    {
      simpl.
      rewrite Rmult_0_r.
      reflexivity.
    }
    {
      simpl.
      rewrite Pos2Nat.inj_mul.
      rewrite mult_INR.
      rewrite <- Ropp_mult_distr_l.
      reflexivity.
    }
    {
      simpl.
      rewrite Pos2Nat.inj_mul.
      rewrite mult_INR.
      rewrite <- Ropp_mult_distr_l.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_involutive.
      reflexivity.
    }
  }
Qed.