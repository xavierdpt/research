Require Import XR_Rsqr.
Require Import XR_Rminus.
Require Import XR_Rmult_plus_distr_l.
Require Import XR_Rmult_plus_distr_r.
Require Import XR_Rplus_assoc.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_Ropp_mult_distr_l.

Local Open Scope R_scope.

Lemma Rsqr_minus_plus : forall a b:R, (a - b) * (a + b) = Rsqr a - Rsqr b.
Proof.
  intros x y.
  unfold Rminus, Rsqr.
  rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  rewrite <- Ropp_mult_distr_l.
  rewrite (Rmult_comm y).
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite <- Ropp_mult_distr_l.
  reflexivity.
Qed.