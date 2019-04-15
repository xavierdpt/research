Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rlt_not_eq.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_dichotomy_converse : forall r1 r2, r1 < r2 \/ r2 < r1 -> r1 <> r2.
Proof.
  intros x y.
  intros [ hxy | hyx ].
  {
    apply Rlt_not_eq.
    exact hxy.
  }
  {
    apply not_eq_sym.
    apply Rlt_not_eq.
    exact hyx.
  }
Qed.



