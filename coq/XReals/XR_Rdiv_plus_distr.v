Require Export XR_Rdiv.
Require Export XR_Rmult_plus_distr_r.

Local Open Scope R_scope.

Lemma Rdiv_plus_distr : forall a b c, (a + b) / c = a / c + b / c.
Proof.
  intros x y z.
  unfold Rdiv.
  rewrite Rmult_plus_distr_r.
  reflexivity.
Qed.
