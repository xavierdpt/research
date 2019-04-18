Require Export XR_mult_IZR.
Require Export XR_pow.

Local Open Scope R_scope.

Lemma pow_IZR : forall z n, pow (IZR z) n = IZR (Z.pow z (Z.of_nat n)).
Proof.
  intros z n.
  generalize dependent z.
  induction n as [ | n hin ].
  {
    intro z.
    simpl.
    reflexivity.
  }
  {
    intro z.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r.
    rewrite mult_IZR.
    rewrite <- hin.
    simpl.
    reflexivity.

    apply Zle_0_nat.
  }
Qed.
