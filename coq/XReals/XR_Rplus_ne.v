Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rplus.
Require Export XR_Rplus_0_l.
Require Export XR_Rplus_0_r.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_ne : forall r, r + R0 = r /\ R0 + r = r.
Proof.
  intros x.
  split.
  { rewrite Rplus_0_r. reflexivity. }
  { rewrite Rplus_0_l. reflexivity. }
Qed.
