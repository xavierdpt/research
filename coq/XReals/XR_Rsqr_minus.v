Require Import XR_Rsqr.
Require Import XR_Rsqr_neg.
Require Import XR_Rsqr_plus.
Require Import XR_R2.
Require Import XR_Rminus.
Require Import XR_Ropp_mult_distr_r.

Local Open Scope R_scope.

Lemma Rsqr_minus : forall x y:R, Rsqr (x - y) = Rsqr x + Rsqr y - R2 * x * y.
Proof.
  intros x y.
  unfold Rminus.
  rewrite Rsqr_plus.
  rewrite <- Rsqr_neg.
  rewrite <- Ropp_mult_distr_r.
  reflexivity.
Qed.