Require Export XR_R.
Require Export XR_Rle.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_le_dec : forall r1 r2, {r1 < r2} + {r2 <= r1}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ hxy | heq ] | hyx ].
  {
    left.
    exact hxy.
  }
  {
    subst y.
    right.
    unfold "<=".
    right.
    reflexivity.
  }
  {
    right.
    unfold "<=".
    left.
    exact hyx.
  }
Qed.
