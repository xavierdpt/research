Require Export XR_R1_neq_R0.
Require Export XR_Rinv_r.
Require Export XR_Rmult_eq_reg_l.

Local Open Scope R_scope.

Lemma Rinv_1 : / R1 = R1.
Proof.
  apply Rmult_eq_reg_l with R1.
  {
    rewrite Rinv_r.
    {
      rewrite Rmult_1_l.
      reflexivity.
    }
    { exact R1_neq_R0. }
  }
  { exact R1_neq_R0. }
Qed.
