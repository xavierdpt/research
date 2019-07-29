Require Import XR_Rsqr.
Require Import XR_Ropp_mult_distr_l.
Require Import XR_Ropp_mult_distr_r.
Require Import XR_Ropp_involutive.

Local Open Scope R_scope.

Lemma Rsqr_neg : forall x:R, Rsqr x = Rsqr (- x).
Proof.
  intro x.
  unfold Rsqr.
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Ropp_mult_distr_r.
  rewrite Ropp_involutive.
  reflexivity.
Qed.
