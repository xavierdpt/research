Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rlt_trans.
Require Export XR_Rlt_irrefl.
Require Export XR_Rle.
Require Export XR_Rplus.
Require Export XR_Rplus_0_r.
Require Export XR_Rplus_lt_compat_l.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_eq_0_l :
  forall r1 r2, R0 <= r1 -> R0 <= r2 -> r1 + r2 = R0 -> r1 = R0.
Proof.
  intros x y.
  intros hx hy heq.
  destruct hx as [ hx | heqx ].
  {
    destruct hy as [ hy | heqy ].
    {
      exfalso.
      apply Rlt_irrefl with R0.
      apply Rlt_trans with x.
      { exact hx. }
      {
        rewrite <- heq.
        pattern x at 1; rewrite <- Rplus_0_r.
        apply Rplus_lt_compat_l.
        exact hy.
      }
    }
    {
      subst y.
      rewrite  Rplus_0_r in heq.
      exact heq.
    }
  }
  {
    subst x.
    reflexivity.
  }
Qed.
