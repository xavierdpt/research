Require Export XR_S_INR.
Require Export XR_Rplus_lt_compat.
Require Export XR_Rlt_0_1.

Local Open Scope R_scope.

Lemma Rlt_0_INR_2 : R0 < INR 2.
Proof.
    rewrite S_INR.
    rewrite <- Rplus_0_r with R0.
    apply Rplus_lt_compat.
    {
      simpl.
      exact Rlt_0_1.
    }
    { exact Rlt_0_1. }
Qed.