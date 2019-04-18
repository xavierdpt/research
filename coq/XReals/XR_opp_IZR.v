Require Export XR_plus_IZR.

Local Open Scope R_scope.

Lemma opp_IZR : forall n:Z, IZR (- n) = - IZR n.
Proof.
  intro n.
  destruct n as [ | n | n ].
  {
    simpl.
    rewrite Ropp_0.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite Ropp_involutive.
    reflexivity.
  }
Qed.
