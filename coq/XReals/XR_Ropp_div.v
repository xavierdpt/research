Require Export XR_Rdiv.
Require Export XR_Ropp_mult_distr_l.

Local Open Scope R_scope.

Lemma Ropp_div : forall x y,
  -x / y = - (x / y).
Proof.
  intros x y.
  unfold Rdiv.
  rewrite <- Ropp_mult_distr_l.
  reflexivity.
Qed.
