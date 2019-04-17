Require Export XR_lt_INR.

Local Open Scope R_scope.

Lemma le_INR : forall n m:nat,
  (n <= m)%nat ->
  INR n <= INR m.
Proof.
  intros n m hnm.
  apply le_lt_or_eq in hnm.
  destruct hnm as [ hlt | heq ].
  {
    unfold "<=".
    left.
    apply lt_INR.
    exact hlt.
  }
  {
    subst m.
    unfold "<=".
    right.
    reflexivity.
  }
Qed.