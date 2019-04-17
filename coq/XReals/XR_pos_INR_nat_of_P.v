Require Export ZArith.
Require Export XR_mult_INR.
Require Export XR_Rlt_0_INR_2.

Local Open Scope R_scope.

Lemma pos_INR_nat_of_P : forall p:positive, R0 < INR (Pos.to_nat p).
Proof.

  intro p.

  induction p as [ p hp | p hp | ].
  {
    rewrite Pos2Nat.inj_xI.
    rewrite S_INR.
    rewrite mult_INR.
    rewrite <- Rplus_0_r with R0.
    apply Rplus_lt_compat.
    {
      apply Rmult_lt_0_compat.
      { exact Rlt_0_INR_2. }
      { apply hp. }
    }
    { exact Rlt_0_1. }
  }
  {
    rewrite Pos2Nat.inj_xO.
    rewrite mult_INR.
    apply Rmult_lt_0_compat.
    { exact Rlt_0_INR_2. }
    { exact hp. }
  }
  {
    simpl.
    exact Rlt_0_1.
  }
Qed.