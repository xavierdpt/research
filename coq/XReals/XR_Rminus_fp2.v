Require Import XR_Rminus_Int_part2.
Require Import XR_frac_part.
Require Import XR_Rlt.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_Rplus_eq_compat_r.
Require Import XR_minus_IZR.

Local Open Scope R_scope.

Lemma Rminus_fp2 : forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2 + R1.
Proof.
  intros x y.
  intro h.
  assert (ip:=Rminus_Int_part2).
  specialize (ip x y).
  specialize (ip h).
  unfold frac_part.
  rewrite ip.
  repeat rewrite minus_IZR.
  simpl.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite Rplus_comm.
  reflexivity.
Qed.
