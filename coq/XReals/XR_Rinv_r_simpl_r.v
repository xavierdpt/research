Require Import XR_Rinv_r.
Require Import XR_Rmult_1_l.

Local Open Scope R_scope.

Lemma Rinv_r_simpl_r : forall r1 r2, r1 <> R0 -> r1 * / r1 * r2 = r2.
Proof.
  intros x y h.
  rewrite Rinv_r.
  {
    rewrite Rmult_1_l.
    reflexivity.
  }
  { exact h. }
Qed.