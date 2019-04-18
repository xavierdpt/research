Require Export XR_total_order_T.
Require Export XR_Rlt_not_eq.

Local Open Scope R_scope.

Lemma Req_EM_T : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ hxy | heq ] | hyx ].
  {
    right.
    apply Rlt_not_eq.
    exact hxy.
  }
  {
    left.
    exact heq.
  }
  {
    right.
    apply not_eq_sym.
    apply Rlt_not_eq.
    exact hyx.
  }
Qed.