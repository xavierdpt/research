Require Export XR_R.
Require Export XR_Rlt_irrefl.
Require Export XR_Rlt_asym.
Require Export XR_Rle.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rle_dec : forall r1 r2, {r1 <= r2} + {~ r1 <= r2}.
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
    unfold "~".
    intro hxy.
    unfold "<=" in hxy.
    destruct hxy as [ hxy | heq ].
    {
      generalize dependent hxy.
      apply Rlt_asym.
      exact hyx.
    }
    {
      subst y.
      generalize dependent hyx.
      apply Rlt_irrefl.
    }
  }
Qed.
