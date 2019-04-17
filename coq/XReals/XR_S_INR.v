Require Export XR_R.
Require Export XR_INR.
Require Export XR_Rplus_0_l.

Local Open Scope R_scope.

Lemma S_INR : forall n:nat, INR (S n) = INR n + R1.
Proof.
  intro n.
  destruct n as [ | n ].
  {
    simpl.
    rewrite Rplus_0_l.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
Qed.
