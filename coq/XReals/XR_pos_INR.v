Require Export XR_S_INR.
Require Export XR_Rplus_le_compat.
Require Export XR_Rlt_0_1.

Local Open Scope R_scope.

Lemma pos_INR : forall n:nat, R0 <= INR n.
Proof.
  induction n as [ | n hn ].
  {
    simpl.
    unfold "<=".
    right.
    reflexivity.
  }
  {
    rewrite S_INR.
    rewrite <- Rplus_0_r with R0.
    apply Rplus_le_compat.
    { exact hn. }
    {
      unfold "<=".
      left.
      exact Rlt_0_1.
    }
  }
Qed.