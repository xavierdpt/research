Require Export XR_INR.

Local Open Scope R_scope.

Lemma INR_not_0 : forall n:nat,
  INR n <> R0 ->
  n <> 0%nat.
Proof.
  intro n.
  destruct n as [ | n ].
  {
    simpl.
    intro h.
    unfold not.
    intro eq.
    unfold not in h.
    apply h.
    reflexivity.
  }
  {
    intro h.
    unfold not.
    intro eq.
    unfold not in h.
    apply h.
    rewrite eq.
    simpl.
    reflexivity.
  }
Qed.
