Require Export XR_frac_part.
Require Export XR_Ropp_le_contravar.
Require Export XR_up_tech.
Require Export XR_IZR_eq.
Require Export XR_Rplus_lt_le_compat.

Local Open Scope R_scope.

Lemma Rminus_Int_part1 : forall r1 r2:R,
  frac_part r2 <= frac_part r1 ->
  Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z.
Proof.
  intros x y.
  unfold frac_part.
  unfold Int_part.
  intro h.
  set (u:=up(x-y)).
  apply eq_IZR.
  repeat rewrite minus_IZR.
  repeat rewrite minus_IZR in h.
  simpl.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  repeat rewrite Rplus_assoc.
  rewrite (Rplus_comm (-R1)).
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  unfold Rminus in h.
  repeat rewrite Ropp_plus_distr in h.
  repeat rewrite Ropp_involutive in h.
  repeat rewrite <- Rplus_assoc in h.
  apply Rplus_le_reg_r in h.
  apply Rplus_eq_reg_r with R1.
  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
  apply Ropp_le_contravar in h.
  repeat rewrite Ropp_plus_distr in h.
  repeat rewrite Ropp_involutive in h.
  rewrite (Rplus_comm (-x)) in h.
  rewrite (Rplus_comm (-y)) in h.

  assert (hax:=archimed x).
  assert (hay:=archimed y).

  destruct hax as [ haxl haxr ].
  destruct hay as [ hayl hayr ].

  assert (ut:=up_tech).

  specialize (ut (x-y)).
  symmetry.

  change R1 with (IZR 1).
  rewrite <- opp_IZR.
  repeat rewrite <- plus_IZR.
  apply IZR_eq.
  fold u in ut.

  specialize (ut (up x - up y))%Z.
  apply ut.

  {
    rewrite minus_IZR.
    apply Rplus_le_reg_r with (-x).
    unfold Rminus.
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm x).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    apply Rplus_le_reg_r with (IZR (up y)).
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm (- IZR (up y))).
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    rewrite (Rplus_comm (-y)).
    exact h.
  }
  {
    rewrite plus_IZR.
    rewrite minus_IZR.
    unfold Rminus.
    repeat rewrite Rplus_assoc.
    apply Rplus_lt_le_compat.
    { exact haxl. }
    {
      apply Rplus_le_reg_l with (IZR (up y)).
      repeat rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_l.
      unfold Rminus in hayr.
      exact hayr.
    }
  }
Qed.