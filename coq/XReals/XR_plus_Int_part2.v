Require Import XR_frac_part.
Require Import XR_Rplus_eq_compat_r.
Require Import XR_IZR_eq.
Require Import XR_up_tech.
Require Import XR_Rplus_le_compat.

Local Open Scope R_scope.

Lemma plus_Int_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < R1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2)%Z.
Proof.
  intros x y.
  unfold frac_part.
  unfold Int_part.
  repeat rewrite minus_IZR.
  set (u:=up(x+y)).
  simpl.
  intro h.
  apply eq_IZR.
  repeat rewrite minus_IZR.
  repeat rewrite plus_IZR.
  repeat rewrite minus_IZR.
  simpl.
  unfold Rminus.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  symmetry.
  change R1 with (IZR 1).
  rewrite <- opp_IZR.
  repeat rewrite <- plus_IZR.
  apply IZR_eq.
  assert (ut:=up_tech).
  specialize (ut (x+y)).
  fold u in ut.
  apply eq_IZR.
  symmetry.
  rewrite <- Rplus_0_r.
  symmetry.
  rewrite <- Rplus_opp_l with R1.
  repeat rewrite <- Rplus_assoc.
  change R1 with (IZR 1).
  rewrite <- opp_IZR.
  repeat rewrite <- plus_IZR.
  apply IZR_eq.
  apply ut.
  {
    repeat rewrite plus_IZR.
    repeat rewrite opp_IZR.
    simpl.
    assert (ax := archimed x).
    assert (ay := archimed y).
    destruct ax as [ axl axr ].
    destruct ay as [ ayl ayr ].
    apply Rplus_le_reg_r with (-(x+y)).
    rewrite Rplus_opp_r.
    apply Rplus_le_reg_r with (R1+R1).
    rewrite Rplus_0_l.
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm (-R1)).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_r, Rplus_0_r.
    rewrite (Rplus_comm (-R1)).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_r, Rplus_0_r.
    rewrite Ropp_plus_distr.
    rewrite (Rplus_comm (IZR (up y))).
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm (-y)).
    set (py:=IZR(up y)+-y).
    rewrite <- Rplus_assoc.
    apply Rplus_le_compat.
    {
      unfold Rminus in axr.
      exact axr.
    }
    {
      unfold py.
      unfold Rminus in ayr.
      exact ayr.
    }
  }
  {
    clear ut.
    clear u.
    repeat rewrite plus_IZR.
    rewrite opp_IZR.
    simpl.
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    unfold Rminus in h.
    repeat rewrite Ropp_plus_distr in h.
    repeat rewrite Ropp_involutive in h.
    repeat rewrite <- Rplus_assoc in h.
    pattern R1 at 3 in h ; rewrite <- Rplus_0_l in h.
    apply Rplus_lt_reg_r in h.
    apply Rplus_lt_reg_r with R1.
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm (-R1)).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    apply (Rplus_lt_compat_r (IZR (up y))) in h.
    repeat rewrite Rplus_assoc in h.
    rewrite Rplus_opp_l in h.
    rewrite Rplus_0_l, Rplus_0_r in h.
    apply (Rplus_lt_compat_r (IZR (up x))) in h.
    repeat rewrite Rplus_assoc in h.
    rewrite (Rplus_comm (-IZR(up x))) in h.
    repeat rewrite Rplus_assoc in h.
    rewrite Rplus_opp_r in h.
    rewrite Rplus_0_r in h.
    rewrite (Rplus_comm R1) in h.
    repeat rewrite <- Rplus_assoc in h.
    repeat rewrite <- Rplus_assoc.
    rewrite (Rplus_comm (IZR(up y))) in h.
    exact h.
  }
Qed.
