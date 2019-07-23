Require Import XR_frac_part.
Require Import XR_Rlt.
Require Import XR_plus_Int_part2.
Require Import XR_plus_IZR.
Require Import XR_Rplus_eq_compat_l.
Require Import XR_Rplus_eq_compat_r.

Local Open Scope R_scope.

Lemma plus_frac_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < R1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2.
Proof.
  intros x y.
  intro h.
  assert (ip := plus_Int_part2).
  specialize (ip x y).
  specialize (ip h).
  clear h.
  unfold frac_part.
  rewrite ip.
  clear ip.
  rewrite plus_IZR.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
Qed.