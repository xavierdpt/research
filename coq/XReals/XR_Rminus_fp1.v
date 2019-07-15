Require Import XR_Rminus_Int_part1.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_Rplus_eq_compat_r.

Local Open Scope R_scope.

Lemma Rminus_fp1 :
  forall r1 r2:R,
    frac_part r2 <= frac_part r1 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2.
Proof.
  intros x y.
  unfold frac_part.
  intro h.
  assert (ip:=Rminus_Int_part1).
  specialize (ip x y).
  unfold frac_part in ip.
  specialize (ip h).
  rewrite ip.
  unfold Rminus.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  rewrite minus_IZR.
  unfold Rminus.
  repeat rewrite Ropp_plus_distr.
  repeat rewrite Ropp_involutive.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
Qed.