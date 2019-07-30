Require Import XR_Rsqr.
Require Import XR_Rinv_mult_distr.

Local Open Scope R_scope.

Lemma Rsqr_inv : forall x:R, x <> R0 -> Rsqr (/ x) = / Rsqr x.
Proof.
  intros x h.
  unfold Rsqr.
  rewrite Rinv_mult_distr.
  { reflexivity. }
  { exact h. }
  { exact h. }
Qed.