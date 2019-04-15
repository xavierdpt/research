Require Export XR_R.
Require Export XR_Rle.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_lt_dec : forall r1 r2, {r1 <= r2} + {r2 < r1}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ hxy | heq ] | hyx ].
  {
    left.
    unfold "<=".
    left.
    exact hxy.
  }
  {
    subst y.
    left.
    unfold "<=".
    right.
    reflexivity.
  }
  {
    right.
    exact hyx.
  }
Qed.
