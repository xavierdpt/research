Require Export XR_Rmult_comm.
Require Export XR_Rmult_lt_compat_l.

Local Open Scope R_scope.

Lemma Rmult_lt_compat_r : forall r r1 r2,
  R0 < r ->
  r1 < r2 ->
  r1 * r < r2 * r.
Proof.
  intros x y z.
  intros hx hyz.
  repeat rewrite (Rmult_comm _ x).
  apply Rmult_lt_compat_l.
  { exact hx. }
  { exact hyz. }
Qed.