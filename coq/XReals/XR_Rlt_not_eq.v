Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rlt_irrefl.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rlt_not_eq : forall r1 r2, r1 < r2 -> r1 <> r2.
Proof.
  intros x y.
  intro hxy.
  unfold not.
  intro eq.
  subst y.
  generalize dependent hxy.
  apply Rlt_irrefl.
Qed.
