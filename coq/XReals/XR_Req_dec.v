Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rlt_irrefl.
Require Export XR_total_order_T.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Req_dec : forall r1 r2, r1 = r2 \/ r1 <> r2.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ hxy | heq ] | hyx ].
  {
    right.
    unfold not.
    intro heq.
    subst y.
    generalize dependent hxy.
    apply Rlt_irrefl.
  }
  {
    left.
    exact heq.
  }
  {
    right.
    unfold not.
    intro heq.
    subst y.
    generalize dependent hyx.
    apply Rlt_irrefl.
  }
Qed.
