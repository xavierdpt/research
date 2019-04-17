Require Export XR_lt_INR.

Local Open Scope R_scope.

Lemma lt_1_INR : forall n:nat,
  (1 < n)%nat ->
  R1 < INR n.
Proof.
  intros n hn.
  replace R1 with (INR 1%nat).
  {
    apply lt_INR.
    exact hn.
  }
  {
    simpl.
    reflexivity.
  }
Qed.