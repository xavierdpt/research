Require Export XR_Rplus_comm.
Require Export XR_Rplus_lt_compat_l.

Local Open Scope R_scope.

Lemma Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
intros x y z.
intro hyz.
repeat rewrite (Rplus_comm _ x).
apply Rplus_lt_compat_l.
exact hyz.
Qed.
