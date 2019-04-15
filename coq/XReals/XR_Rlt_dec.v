Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rlt_irrefl.
Require Export XR_Rlt_asym.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_dec : forall r1 r2, {r1 < r2} + {~ r1 < r2}.
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
    apply Rlt_irrefl.
  }
  {
    right.
    apply Rlt_asym.
    exact hyx.
  }
Qed.