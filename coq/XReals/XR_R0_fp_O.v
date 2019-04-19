Require Export XR_fp_R0.

Local Open Scope R_scope.

Lemma R0_fp_O : forall r:R, R0 <> frac_part r -> R0 <> r.
Proof.
  intros x h.
  unfold not.
  intro heq.
  subst x.
  unfold not in h.
  apply h.
  clear h.
  rewrite fp_R0.
  reflexivity.
Qed.

