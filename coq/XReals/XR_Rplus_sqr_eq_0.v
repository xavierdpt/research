Require Export XR_Rplus_sqr_eq_0_l.

Local Open Scope R_scope.

Lemma Rplus_sqr_eq_0 : forall r1 r2,
  Rsqr r1 + Rsqr r2 = R0 ->
  r1 = R0 /\ r2 = R0.
Proof.
  intros x y h.
  split.
  {
    apply Rplus_sqr_eq_0_l with y.
    exact h.
  }
  {
    apply Rplus_sqr_eq_0_l with x.
    rewrite Rplus_comm.
    exact h.
  }
Qed.