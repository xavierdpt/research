Require Export XR_Rlt_minus.
Require Export XR_Rle.

Local Open Scope R_scope.

Lemma Rle_minus : forall r1 r2,
  r1 <= r2 ->
  r1 - r2 <= R0.
Proof.
  intros x y h.
  unfold "<=" in h.
  destruct h as [ h | heq ].
  {
    unfold "<=".
    left.
    apply Rlt_minus.
    exact h.
  }
  {
    subst y.
    unfold Rminus.
    rewrite Rplus_opp_r.
    unfold "<=".
    right.
    reflexivity.
  }
Qed.