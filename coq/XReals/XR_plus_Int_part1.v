Require Import XR_frac_part.
Require Import XR_Rplus_eq_compat_r.
Require Import XR_tech_up.
Require Import XR_IZR_eq.
Require Import XR_Rplus_lt_compat.
Require Import XR_Rplus_eq_compat_l.

Local Open Scope R_scope.

Lemma plus_Int_part1 : forall r1 r2:R,
  R1 <= frac_part r1 + frac_part r2 ->
  Int_part (r1 + r2) = (Int_part r1 + Int_part r2 + 1)%Z.
Proof.
  intros x y.
  unfold frac_part.
  unfold Int_part.
  repeat rewrite minus_IZR.
  simpl.
  intro h.
  unfold Rminus in h.
  repeat rewrite Ropp_plus_distr in h.
  repeat rewrite Ropp_involutive in h.
  pattern R1 at 1 in h ; rewrite <- Rplus_0_l in h.
  repeat rewrite <- Rplus_assoc in h.
  apply Rplus_le_reg_r in h.
  apply eq_IZR.
  repeat rewrite minus_IZR.
  repeat rewrite plus_IZR.
  repeat rewrite minus_IZR.
  simpl.
  unfold Rminus.
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_r.
  rewrite (Rplus_comm  (-R1)).
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  set (u := up(x+y)).
  assert (tu := tech_up).
  specialize (tu (x+y)).
  fold u in tu.
  symmetry.
  rewrite <- plus_IZR.
  apply IZR_eq.
  apply tu; clear tu.
  {
    rewrite plus_IZR.
    assert (ax := archimed x).
    assert (ay := archimed y).
    destruct ax as [ axl axr ].
    destruct ay as [ ayl ayr ].
    apply Rplus_lt_compat.
    { exact axl. }
    { exact ayl. }
  }
  {
    rewrite plus_IZR.
    apply Rplus_le_reg_r with (-(IZR (up x)+IZR(up y))).
    rewrite Rplus_opp_r.
    eapply Rle_trans.
    exact h.
    right.
    repeat rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    rewrite Ropp_plus_distr.
    repeat rewrite <- Rplus_assoc.
    apply Rplus_eq_compat_r.
    rewrite Rplus_comm.
    repeat rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    rewrite Rplus_comm.
    reflexivity.
  }
Qed.
