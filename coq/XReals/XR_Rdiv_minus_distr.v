Require Export XR_Rmult_plus_distr_r.
Require Export XR_Ropp_mult_distr_l.
Require Export XR_Rminus.
Require Export XR_Rdiv.

Local Open Scope R_scope.

Lemma Rdiv_minus_distr : forall a b c, (a - b)/c = a/c - b/c.
Proof.
  intros x y z.
  unfold Rminus, Rdiv.
  rewrite Rmult_plus_distr_r.
  rewrite <- Ropp_mult_distr_l.
  reflexivity.
Qed.
