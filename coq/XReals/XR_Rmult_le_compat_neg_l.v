Require Export XR_Rmult_le_compat_l.
Require Export XR_Ropp_le_cancel.
Require Export XR_Ropp_mult_distr_l.
Require Export XR_Ropp_0.

Local Open Scope R_scope.

Lemma Rmult_le_compat_neg_l : forall r r1 r2,
  r <= R0 ->
  r1 <= r2 ->
  r * r2 <= r * r1.
Proof.
  intros x y z.
  intros hx hyz.
  apply Ropp_le_cancel.
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_l.
  {
    rewrite <- Ropp_0.
    apply Ropp_le_contravar.
    exact hx.
  }
  { exact hyz. }
Qed.