Require Import XR_frac_part.
Require Import XR_Rle.
Require Import XR_plus_Int_part1.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_plus_IZR.
Require Import XR_Rplus_eq_compat_r.

Local Open Scope R_scope.

Lemma plus_frac_part1 :
  forall r1 r2:R,
    R1 <= frac_part r1 + frac_part r2->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2 - R1.
Proof.
  intros x y.
  intro h.
  unfold frac_part.
  assert (pi := plus_Int_part1).
  specialize (pi x y).
  specialize (pi h).
  rewrite pi.
  clear pi h.
  unfold Rminus.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  repeat rewrite plus_IZR.
  repeat rewrite Ropp_plus_distr.
  simpl.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
Qed.
