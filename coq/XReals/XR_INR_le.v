Require Export XR_INR_lt.
Require Export XR_INR_eq.
Require Export XR_Rle.

Local Open Scope R_scope.

Lemma INR_le : forall n m:nat, INR n <= INR m -> (n <= m)%nat.
Proof.
  intros n m h.
  unfold "<=" in h.
  destruct h as [ hlt | heq ].
  {
    apply Nat.lt_succ_r.
    apply Nat.lt_lt_succ_r.
    apply INR_lt.
    exact hlt.
  }
  {
    apply Nat.eq_le_incl.
    apply INR_eq.
    exact heq.
  }
Qed.