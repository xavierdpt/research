Require Import XR_nonzeroreal.
Require Import XR_Rsqr.
Require Import XR_Rdiv.
Require Import XR_Rmult.
Require Import XR_Rplus.
Require Import XR_Rminus.
Require Import XR_R2.
Require Import XR_R4.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_Rinv_mult_distr.
Require Import XR_Rmult_plus_distr_r.
Require Import XR_double.
Require Import XR_Ropp_mult_distr_l.
Require Import XR_R2_neq_R0.
Require Import XR_R4_neq_R0.

Local Open Scope R_scope.

Lemma canonical_Rsqr :
  forall (a:nonzeroreal) (b c x:R),
    a * Rsqr x + b * x + c =
    a * Rsqr (x + b / (R2 * a)) + (R4 * a * c - Rsqr b) / (R4 * a).
Proof.
intros a b c x.
symmetry.
unfold Rminus, Rdiv, Rsqr, R4.
repeat rewrite Rinv_mult_distr.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/a)).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm a).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (Rmult_comm a).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R2)).
rewrite (Rmult_comm x (b * _)).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R2)).
repeat rewrite <- Rplus_assoc.
repeat rewrite <- Rmult_assoc.
rewrite <- double.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R2).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite (Rmult_comm a).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (Rmult_comm a).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Rplus_comm.
repeat rewrite Rmult_assoc.
repeat rewrite <- Rplus_assoc.
rewrite <- Rmult_plus_distr_r.
fold R4.
rewrite (Rmult_comm R4).
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R2)).
repeat rewrite Rmult_assoc.
rewrite <- (Rinv_mult_distr R2).
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
fold R2.
fold R4.
rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R4)).
rewrite (Rmult_comm (/a)).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/a)).
repeat rewrite Rmult_assoc.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.

exact R2_neq_R0.
exact R2_neq_R0.
exact R4_neq_R0.
apply cond_nonzero.
apply cond_nonzero.
exact R2_neq_R0.
apply cond_nonzero.
apply cond_nonzero.
fold R4. exact R4_neq_R0.
apply cond_nonzero.
exact R2_neq_R0.
apply cond_nonzero.
Qed.