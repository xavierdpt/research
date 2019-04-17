Require Export XR_INR.
Require Export XR_IZR.

Local Open Scope R_scope.

Lemma INR_IZR_INZ : forall n:nat, INR n = IZR (Z.of_nat n).
Proof.
  intro n.
  induction n as [ | n hin ].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite SuccNat2Pos.id_succ.
    reflexivity.
  }
Qed.
