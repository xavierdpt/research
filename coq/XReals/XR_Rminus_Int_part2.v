Require Import XR_frac_part.
Require Import XR_Rplus_eq_compat_r.
Require Import XR_tech_up.
Require Import XR_IZR_eq.
Require Import XR_Rplus_le_compat.
Require Import XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma Rminus_Int_part2 :
  forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2 - 1)%Z.
Proof.
  intros x y.
  unfold frac_part.
  unfold Int_part.
  intro h.
  set (u:=up(x-y)).
  apply eq_IZR.
  repeat rewrite minus_IZR.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  simpl.
  repeat rewrite Rplus_assoc.
  rewrite (Rplus_comm (-R1)).
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  repeat rewrite minus_IZR in h.
  unfold Rminus in h.
  repeat rewrite Ropp_plus_distr in h.
  repeat rewrite Ropp_involutive in h.
  repeat rewrite <- Rplus_assoc in h.
  apply Rplus_lt_reg_r in h.
  apply Ropp_lt_contravar in h.
  repeat rewrite Ropp_plus_distr in h.
  repeat rewrite Ropp_involutive in h.
  rewrite (Rplus_comm (-y)) in h.
  rewrite (Rplus_comm (-x)) in h.

  assert (hax := archimed x).
  assert (hay := archimed y).
  assert (tu := tech_up).
  specialize (tu (x-y)).
  fold u in tu.
  symmetry.
  unfold Rminus in hax, hay.
  destruct hax as [ haxl haxr ].
  destruct hay as [ hayl hayr ].

  rewrite <- opp_IZR.
  rewrite <- plus_IZR.
  apply IZR_eq.
  apply tu; clear tu.
  {
    rewrite plus_IZR.
    rewrite opp_IZR.
    unfold Rminus.
    apply Rplus_lt_reg_r with (-x).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_comm with x _.
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    apply Rplus_lt_reg_r with (IZR (up y)).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_comm with (-IZR(up y)) _.
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    rewrite Rplus_comm.
    exact h.
  }
  {
    clear h.
    rewrite plus_IZR.
    rewrite opp_IZR.
    unfold Rminus.
    repeat rewrite Rplus_assoc.
    apply Rplus_le_reg_r with (-x).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_comm with x _.
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    rewrite Rplus_comm with _ (-x).
    rewrite Rplus_comm with _ R1.
    repeat rewrite <- Rplus_assoc.
    apply Rplus_le_compat.
    { exact haxr. }
    {
      apply Ropp_le_contravar.
      left.
      exact hayl.
    }
  }
Qed.
