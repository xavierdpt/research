Require Import XRbase.
Require Import XRbasic_fun.
Local Open Scope XR_scope.

Lemma Rsqr_neg : forall x:R, Rsqr x = Rsqr (- x).
Proof.
  intro x.
  unfold Rsqr.
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Ropp_mult_distr_r.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma Rsqr_mult : forall x y:R, Rsqr (x * y) = Rsqr x * Rsqr y.
Proof.
  intros x y.
  unfold Rsqr.
  pose (p:=x*y).
  fold p.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm x).
  rewrite <- Rmult_assoc.
  fold p.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm y).
  fold p.
  reflexivity.
Qed.

Lemma Rsqr_plus : forall x y:R, Rsqr (x + y) = Rsqr x + Rsqr y + (IZR 2) * x * y.
Proof.
  intros x y.
  unfold Rsqr.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  unfold IZR.
  unfold IPR.
  unfold IPR_2.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r.
  repeat (rewrite Rplus_assoc).
  rewrite (Rmult_1_l).
  apply Rplus_eq_compat_l.
  rewrite Rplus_comm.
  repeat (rewrite <- Rplus_assoc).
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  apply Rplus_eq_compat_l.
  rewrite Rmult_comm.
  reflexivity.
Qed.

Lemma Rsqr_minus : forall x y:R, Rsqr (x - y) = Rsqr x + Rsqr y - (IZR 2) * x * y.
Proof.
  intros x y.
  unfold Rsqr.
  unfold Rminus.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r.
  unfold IZR. unfold IPR. unfold IPR_2.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  rewrite Ropp_plus_distr.
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Ropp_mult_distr_r.
  rewrite <- Ropp_mult_distr_r.
  rewrite Ropp_involutive.
  repeat (rewrite Rplus_assoc).
  apply Rplus_eq_compat_l.
  rewrite Rplus_comm.
  repeat (rewrite <- Rplus_assoc).
  rewrite Rplus_comm.
  rewrite (Rplus_comm (y*y)).
  rewrite (Rmult_comm y).
  repeat (rewrite Rplus_assoc).
  apply Rplus_eq_compat_l.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma Rsqr_neg_minus : forall x y:R, Rsqr (x - y) = Rsqr (y - x).
Proof.
  intros x y.
  unfold Rsqr.
  unfold Rminus.
  repeat(rewrite Rmult_plus_distr_r).
  repeat(rewrite Rmult_plus_distr_l).
  repeat (rewrite <- Ropp_mult_distr_l).
  repeat (rewrite <- Ropp_mult_distr_r).
  repeat (rewrite Ropp_involutive).
  repeat (rewrite Rplus_assoc).
  rewrite Rplus_comm.
  repeat (rewrite <- Rplus_assoc).
  apply Rplus_eq_compat_r.
  repeat (rewrite Rplus_assoc).
  rewrite Rplus_comm.
  repeat (rewrite <- Rplus_assoc).
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma Rsqr_1 : Rsqr R1 = R1.
Proof.
  unfold Rsqr.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma Rsqr_gt_0_0 : forall x:R, R0 < Rsqr x -> x <> R0.
Proof.
  unfold Rsqr.
  intros x h.
  destruct (Rtotal_order x R0) as [ lt | [ eq | gt ]].
  apply Rlt_not_eq. assumption.
  subst x. rewrite Rmult_0_r in h.
  apply Rlt_not_eq. assumption.
  apply Rlt_not_eq'. assumption.
Qed.

Lemma Rsqr_pos_lt : forall x:R, x <> R0 -> R0 < Rsqr x.
Proof.
  intros x h.
  unfold Rsqr.
  destruct (Rtotal_order x R0) as [ lt | [ eq | gt ]].
  rewrite <- Ropp_involutive with (x*x).
  rewrite Ropp_mult_distr_r.
  rewrite Ropp_mult_distr_l.
  apply Rmult_lt_0_compat.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar. assumption.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar. assumption.
  subst x. exfalso. apply h. reflexivity.
  apply Rmult_lt_0_compat. assumption. assumption.
Qed.

Lemma Rsqr_div : forall x y:R, y <> R0 -> Rsqr (x / y) = Rsqr x / Rsqr y.
Proof.
  intros x y h.
  unfold Rsqr.
  unfold Rdiv.
  rewrite Rinv_mult_distr.
  repeat (rewrite <- Rmult_assoc).
  apply Rmult_eq_compat_r.
  repeat (rewrite Rmult_assoc).
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm. reflexivity.
  assumption.
  assumption.
Qed.

Lemma Rsqr_eq_0 : forall x:R, Rsqr x = R0 -> x = R0.
Proof.
  unfold Rsqr.
  intros x h.
  destruct (Rtotal_order x R0) as [ lt | [ eq | gt ]].
  apply Rmult_eq_reg_r with x. rewrite h. rewrite Rmult_0_l. reflexivity.
  apply Rlt_not_eq. assumption.
  assumption.
  apply Rmult_eq_reg_r with x. rewrite h. rewrite Rmult_0_l. reflexivity.
  apply Rlt_not_eq'. assumption.
Qed.

Lemma Rsqr_minus_plus : forall a b:R, (a - b) * (a + b) = Rsqr a - Rsqr b.
Proof.
  unfold Rsqr.
  intros a b.
  unfold Rminus.
  repeat (rewrite Rmult_plus_distr_l).
  repeat (rewrite Rmult_plus_distr_r).
  repeat (rewrite Rplus_assoc).
  apply Rplus_eq_compat_l.
  repeat (rewrite <- Ropp_mult_distr_l).
  repeat (rewrite <- Rplus_assoc).
  rewrite (Rmult_comm a).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rsqr_plus_minus : forall a b:R, (a + b) * (a - b) = Rsqr a - Rsqr b.
Proof.
  unfold Rsqr, Rminus.
  intros a b.
  repeat (rewrite Rmult_plus_distr_l).
  repeat (rewrite Rmult_plus_distr_r).
  repeat (rewrite <- Ropp_mult_distr_r).
  repeat (rewrite Rplus_assoc).
  apply Rplus_eq_compat_l.
  repeat (rewrite <- Rplus_assoc).
  rewrite (Rmult_comm b).
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rsqr_incr_0 :
  forall x y:R, Rsqr x <= Rsqr y -> R0 <= x -> R0 <= y -> x <= y.
Proof.
  unfold Rsqr.
  intros x y.
  intro hsqr.
  intros hx hy.
  destruct hx.
  2:{
    subst x. assumption.
  }
  destruct hy.
  2:{
    subst y.
    destruct hsqr.
    2: {
      right. rewrite Rmult_0_r in H0.
      apply Rsqr_eq_0. fold (Rsqr x) in H0. assumption.
    }
    exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x.
    assumption.
    rewrite Rmult_0_r in H0.
    apply Rmult_lt_reg_l with x. assumption.
    rewrite Rmult_0_r. assumption.
  }
  destruct hsqr.
  2:{
    right.
    destruct (Rtotal_order x y) as [ lt | [ eq | gt ]].
    exfalso. apply Rlt_irrefl with x. apply Rmult_lt_reg_l with x.
    assumption. pattern (x*x) at 2. rewrite H1.
    apply Rmult_le_0_lt_compat.
    left;assumption.
    left;assumption.
    assumption.
    assumption.
    assumption.
    exfalso. apply Rlt_irrefl with y. apply Rmult_lt_reg_l with y.
    assumption. pattern (y*y) at 2;rewrite <- H1.
    apply Rmult_le_0_lt_compat.
    left;assumption.
    left;assumption.
    assumption.
    assumption.
  }
  left.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ]].
  assumption.
  subst y. exfalso. apply Rlt_irrefl with (x*x). assumption.
  exfalso. apply Rlt_irrefl with y.
  apply Rmult_lt_reg_l with y. assumption.
  apply Rlt_trans with (x*x).
  apply Rmult_le_0_lt_compat.
  left. assumption.
  left. assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma Rsqr_incr_0_var : forall x y:R, Rsqr x <= Rsqr y -> R0 <= y -> x <= y.
Proof.
  unfold Rsqr.
  intros x y hsqr hy.
  destruct hy.
  2:{
    subst y.
    destruct hsqr.
    2:{
      right.
      apply Rsqr_eq_0.
      unfold Rsqr. rewrite H. rewrite Rmult_0_l. reflexivity.
    }
    left. rewrite Rmult_0_l in H.
    destruct (Rle_0_sqr x).
    2:{
      unfold Rsqr in H0. rewrite <- H0 in H.
      exfalso. apply Rlt_irrefl with R0. assumption.
    }
    unfold Rsqr in H0. exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with (x*x);assumption.
  }
  destruct hsqr.
  2:{
    destruct (Rtotal_order x y).
    left. assumption.
    destruct H1. right. assumption.
    exfalso. apply Rlt_irrefl with (x*x).
    pattern (x*x) at 1;rewrite H0.
    apply Rmult_gt_0_lt_compat.
    assumption.
    apply Rlt_trans with y. assumption. assumption.
    assumption. assumption.
  }
  destruct (Rtotal_order x y).
  left. assumption.
  destruct H1.
  subst  y. right. reflexivity.
  exfalso. apply Rlt_irrefl with y.
  apply Rlt_trans with x. assumption.
  apply Rmult_lt_reg_r with y. assumption.
  apply Rlt_trans with (x*x).
  apply Rmult_lt_compat_l.
  apply Rlt_trans with y. assumption. assumption.
  assumption.
  assumption.
Qed.

Lemma Rsqr_incr_1 :
  forall x y:R, x <= y -> R0 <= x -> R0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y hxy hx hy.
  unfold Rsqr.
  apply Rmult_le_compat.
  assumption. assumption. assumption. assumption.
Qed.

Lemma Rsqr_incrst_0 :
  forall x y:R, Rsqr x < Rsqr y -> R0 <= x -> R0 <= y -> x < y.
Proof.
  unfold Rsqr.
  intros x y h hx hy.
  destruct hx.
  2:{
    subst x.
    destruct hy.
    2:{
      subst y. repeat (rewrite Rmult_0_l in h). assumption.
    }
    assumption.
  }
  destruct hy.
  2:{
    subst y. exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with x.
    assumption.
    apply Rmult_lt_reg_l with x. assumption.
    rewrite Rmult_0_r.
    rewrite Rmult_0_r in h.
    assumption.
  }
  destruct (Rtotal_order x y).
  assumption.
  destruct H1.
  subst y. apply Rlt_irrefl in h. contradiction.
  exfalso. apply Rlt_irrefl with y. apply Rlt_trans with x.
  assumption. apply Rmult_lt_reg_l with x. assumption.
  apply Rlt_trans with (y*y). assumption.
  apply Rmult_lt_compat_r. assumption. assumption.
Qed.

Lemma Rsqr_incrst_1 :
  forall x y:R, x < y -> R0 <= x -> R0 <= y -> Rsqr x < Rsqr y.
Proof.
  intros x y hxy hx hy.
  unfold Rsqr.
  apply Rmult_le_0_lt_compat.
  assumption. assumption. assumption. assumption.
Qed.

Lemma Rsqr_neg_pos_le_0 :
  forall x y:R, Rsqr x <= Rsqr y -> R0 <= y -> - y <= x.
Proof.
  intros x y h hy.
  destruct hy as [ hy | eqy ].
  2:{ (* Case y = 0 *)
    (* Rewriting and simplifications *)
    subst y. rewrite Ropp_0. rewrite Rsqr_0 in h.
    (* Choose to show that x = 0 *)
    right. symmetry.
    apply Rsqr_eq_0. (* x² = 0 -> x = 0 *)
    (* Now we can use antisymmetry to show the equality *)
    apply Rle_antisym.
    - exact h.
    - apply Rle_0_sqr. (* 0 <= r² *)
  }
  (* Now we're left with 0 < y *)
  destruct h as [hlt | heq].
  2:{ (* x² = y² *)
    (* Some rewriting *)
    apply (Rplus_eq_compat_r (-(Rsqr y))) in heq.
    rewrite Rplus_opp_r in heq.
    fold (Rsqr x - Rsqr y) in heq.
    (* Identity (a + b) * (a - b) = a² - b² *)
    rewrite <- Rsqr_plus_minus in heq.
    (* x + y = 0 or x - y = 0 *)
    apply Rmult_integral in heq.
    destruct heq as [ hplus | hminus ].
    { (* x + y = 0 *)
      (* rewrite to x = -y *)
      apply (Rplus_eq_compat_r (-y)) in hplus.
      rewrite Rplus_0_l in hplus.
      rewrite Rplus_assoc in hplus.
      rewrite Rplus_opp_r in hplus.
      rewrite Rplus_0_r in hplus.
      (* trivial *)
      subst x. right. reflexivity.
    }
    { (* x - y = 0 *)
      (* rewrite to x = y *)
      apply (Rplus_eq_compat_r y) in hminus.
      rewrite Rplus_0_l in hminus.
      unfold Rminus in hminus.
      rewrite Rplus_assoc in hminus.
      rewrite Rplus_opp_l in hminus.
      rewrite Rplus_0_r in hminus.
      (* substitution *)
      subst x.
      (* We can use transitivity to show -y <= y with 0 < y *)
      left. apply Rlt_trans with R0.
      - rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
      - assumption.
    }
  }
  (* We now distinguish between the cases 0 < x, 0 = x and 0 > x *)
  destruct (Rtotal_order R0 x) as [ xpos | [ xnul | xneg ] ].
  { (* 0 < x *)
    left.
    apply Rlt_trans with (-x).
    + apply Ropp_lt_contravar.
      apply Rsqr_incrst_0.
      - assumption.
      - left. assumption.
      - left. assumption.
    + apply Rlt_trans with R0.
      - rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
      - assumption.
  }
  { (* 0 = x *)
    subst x. left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  }
  {
    left.
    rewrite <- Ropp_involutive with x.
    apply Ropp_lt_contravar.
    apply Rsqr_incrst_0.
    + rewrite <- Rsqr_neg. assumption.
    + left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
    + left. assumption.
  }
Qed.

Lemma Rsqr_neg_pos_le_1 :
  forall x y:R, - y <= x -> x <= y -> R0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y hbot htop hy.
  destruct hy.
  2:{
    subst y. right. rewrite Rsqr_0.
    unfold Rsqr.
    apply Rmult_eq_0_compat.
    left.
    apply Rle_antisym. assumption. rewrite Ropp_0 in hbot. assumption.
  }
  destruct htop.
  2:{
    subst y. right. reflexivity.
  }
  destruct hbot.
  2:{
    subst x. rewrite <- Rsqr_neg. right. reflexivity.
  }
  left.
  unfold Rsqr.
  destruct (Rtotal_order R0 x).
  apply Rmult_le_0_lt_compat.
  left;assumption.
  left;assumption.
  assumption.
  assumption.
  destruct H2. subst x.
  apply Rmult_le_0_lt_compat.
  right;reflexivity.
  right;reflexivity.
  assumption.
  assumption.
  rewrite <- Ropp_involutive with (x*x).
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_r.
  apply Rmult_le_0_lt_compat.
  left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  rewrite <- Ropp_involutive with y. apply Ropp_lt_contravar. assumption.
  rewrite <- Ropp_involutive with y. apply Ropp_lt_contravar. assumption.
Qed.

Lemma neg_pos_Rsqr_le : forall x y:R, - y <= x -> x <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y hbot htop.
  destruct (Rtotal_order R0 y) as [ hlt | [ heq | hgt ] ].
  { apply Rsqr_neg_pos_le_1. assumption. assumption. left. assumption. }
  { apply Rsqr_neg_pos_le_1. assumption. assumption. right. assumption. }
  {
    destruct hbot.
    2:{
      subst x. rewrite <- Rsqr_neg. right. reflexivity.
    }
    destruct htop.
    2:{
      subst y. right. reflexivity.
    }
    destruct (Rtotal_order R0 x).
    {
      rewrite Rsqr_neg with y.
      unfold Rsqr.
      left.
      apply Rmult_le_0_lt_compat.
      left;assumption. left;assumption.
      apply Rlt_trans with y. assumption.
      apply Rlt_trans with R0. assumption.
      rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
      apply Rlt_trans with y. assumption.
      apply Rlt_trans with R0. assumption.
      rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
    }
    destruct H1.
    { subst x. exfalso. apply Rlt_irrefl with R0. apply Rlt_trans with y;assumption. }
    {
      exfalso.
      apply Rlt_irrefl with (-y).
      apply Rlt_trans with x. assumption.
      apply Rlt_trans with y. assumption.
      apply Rlt_trans with R0. assumption.
      rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
    }
  }
Qed.

Lemma Rsqr_abs : forall x:R, Rsqr x = Rsqr (Rabs x).
Proof.
  intros x.
  unfold Rsqr.
  unfold Rabs. destruct (Rcase_abs x).
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Ropp_mult_distr_r.
  rewrite Ropp_involutive.
  reflexivity.
  reflexivity.
Qed.

Lemma Rsqr_le_abs_0 : forall x y:R, Rsqr x <= Rsqr y -> Rabs x <= Rabs y.
Proof.
  intros x y h.
  apply Rsqr_incr_0.
  rewrite <- Rsqr_abs.
  rewrite <- Rsqr_abs.
  assumption.
  apply Rabs_pos.
  apply Rabs_pos.
Qed.

Lemma Rsqr_le_abs_1 : forall x y:R, Rabs x <= Rabs y -> Rsqr x <= Rsqr y.
Proof.
  intros x y h.
  rewrite (Rsqr_abs x).
  rewrite (Rsqr_abs y).
  apply Rsqr_incr_1. assumption.
  apply Rabs_pos.
  apply Rabs_pos.
Qed.

Lemma Rsqr_lt_abs_0 : forall x y:R, Rsqr x < Rsqr y -> Rabs x < Rabs y.
Proof.
  intros x y h.
  apply Rsqr_incrst_0.
  rewrite <- Rsqr_abs.
  rewrite <- Rsqr_abs.
  assumption.
  apply Rabs_pos.
  apply Rabs_pos.
Qed.


Lemma Rsqr_lt_abs_1 : forall x y:R, Rabs x < Rabs y -> Rsqr x < Rsqr y.
Proof.
  intros.
  rewrite (Rsqr_abs x).
  rewrite (Rsqr_abs y).
  apply Rsqr_incrst_1.
  assumption.
  apply Rabs_pos.
  apply Rabs_pos.
Qed.

Lemma Rsqr_inj : forall x y:R, R0 <= x -> R0 <= y -> Rsqr x = Rsqr y -> x = y.
Proof.
  intros x y hx hy heq.
  apply Rle_antisym.
  apply Rsqr_incr_0. right. assumption.
  assumption. assumption.
  apply Rsqr_incr_0. right. symmetry. assumption.
  assumption. assumption.
Qed.

Lemma Rsqr_eq_abs_0 : forall x y:R, Rsqr x = Rsqr y -> Rabs x = Rabs y.
Proof.
  intros x y h.
  unfold Rabs.
  destruct (Rcase_abs x);destruct (Rcase_abs y).
  apply Rsqr_inj.
  left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  rewrite <- Rsqr_neg. rewrite <- Rsqr_neg. assumption.
  apply Rsqr_inj.
  left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  assumption.
  rewrite <- Rsqr_neg. assumption.
  apply Rsqr_inj.
  assumption.
  left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  rewrite <- Rsqr_neg. assumption.
  apply Rsqr_inj.
  assumption.
  assumption.
  assumption.
Qed.

Lemma Rsqr_eq_asb_1 : forall x y:R, Rabs x = Rabs y -> Rsqr x = Rsqr y.
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs x);destruct (Rcase_abs y);intros.
  apply Ropp_eq_compat in H. repeat (rewrite Ropp_involutive in H).
  subst y. reflexivity.
  subst y. rewrite <- Rsqr_neg. reflexivity.
  subst x. rewrite <- Rsqr_neg. reflexivity.
  subst y. reflexivity.
Qed.

(* TODO *)
Lemma triangle_rectangle :
  forall x y z:R,
    R0 <= z -> Rsqr x + Rsqr y <= Rsqr z -> - z <= x <= z /\ - z <= y <= z.
Proof.
(*
  Rplus_le_reg_pos_r
    0 <= r2 ->
    r1 + r2 <= r3 ->
    r1 <= r3

  Rsqr_neg_pos_le_0
    x² <= y² ->
    0 <= y ->
    - y <= x

  Rle_0_sqr 
    0 <= r²

  Rsqr_incr_0_var :
    x² <= y² ->
    0 <= y ->
    x <= y


*)
  intros.
  split.
  { split.
    {
      apply Rsqr_neg_pos_le_0.
      {
        apply Rplus_le_reg_pos_r with (Rsqr y).
        { apply Rle_0_sqr. }
        { assumption. }
      }
      { assumption. }
    }
apply Rsqr_incr_0_var.
apply Rplus_le_reg_pos_r with (Rsqr y).
apply Rle_0_sqr. assumption. assumption.
}
split.
apply Rsqr_neg_pos_le_0.
apply Rplus_le_reg_pos_r with (Rsqr x).
apply Rle_0_sqr. rewrite Rplus_comm. assumption. assumption.
apply Rsqr_incr_0_var. 
apply Rplus_le_reg_pos_r with (Rsqr x).
apply Rle_0_sqr. rewrite Rplus_comm. assumption. assumption.
Qed.

(* TODO *)
Lemma triangle_rectangle_lt :
  forall x y z:R,
    Rsqr x + Rsqr y < Rsqr z -> Rabs x < Rabs z /\ Rabs y < Rabs z.
Proof.
  intros; split;
    [ generalize (plus_lt_is_lt (Rsqr x) (Rsqr y) (Rsqr z) (Rle_0_sqr y) H);
      intro; apply Rsqr_lt_abs_0; assumption
      | rewrite Rplus_comm in H;
        generalize (plus_lt_is_lt (Rsqr y) (Rsqr x) (Rsqr z) (Rle_0_sqr x) H);
          intro; apply Rsqr_lt_abs_0; assumption ].
Qed.

(* TODO *)
Lemma triangle_rectangle_le :
  forall x y z:R,
    Rsqr x + Rsqr y <= Rsqr z -> Rabs x <= Rabs z /\ Rabs y <= Rabs z.
Proof.
  intros; split;
    [ generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (Rle_0_sqr y) H);
      intro; apply Rsqr_le_abs_0; assumption
      | rewrite Rplus_comm in H;
        generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (Rle_0_sqr x) H);
          intro; apply Rsqr_le_abs_0; assumption ].
Qed.

Lemma Rsqr_inv : forall x:R, x <> R0 -> Rsqr (/ x) = / Rsqr x.
Proof.
  intros x h.
  unfold Rsqr.
  rewrite Rinv_mult_distr. reflexivity.
  assumption. assumption.
Qed.

(* Coq would shine if there was a natural way to do this kind of stuff *)
Lemma canonical_Rsqr :
  forall (a:nonzeroreal) (b c x:R),
    a * Rsqr x + b * x + c =
    a * Rsqr (x + b / ((IZR 2) * a)) + ((IZR 4) * a * c - Rsqr b) / ((IZR 4) * a).
Proof.

  assert (neq20 : IZR 2 <> R0).
  {
    unfold IZR. unfold IPR. unfold IPR_2. intro h.
    apply Rlt_irrefl with R0. pattern R0 at 2;rewrite <- h.
    apply Rlt_trans with R1. apply Rlt_0_1.
    apply Rplus_lt_reg_l with (-R1).
    rewrite Rplus_opp_l. rewrite <- Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_l. apply Rlt_0_1.
  }

  assert (neq40 : IZR 4 <> R0).
  {
    intro eq.
    apply Rlt_irrefl with R0.
    pattern R0 at 2;rewrite <- eq.
    unfold IZR. unfold IPR. unfold IPR_2.
    rewrite Rmult_plus_distr_l.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_r.
    apply Rlt_trans with R1.
    apply Rlt_0_1.
    apply Rplus_lt_reg_r with (-R1).
    rewrite Rplus_opp_r.
    apply Rlt_trans with R1.
    apply Rlt_0_1.
    apply Rplus_lt_reg_r with (-R1).
    rewrite Rplus_opp_r.
    apply Rlt_trans with R1.
    apply Rlt_0_1.
    apply Rplus_lt_reg_r with (-R1).
    rewrite Rplus_opp_r.
    repeat (rewrite Rplus_assoc).
    rewrite <- (Rplus_assoc R1 (-R1)).
    rewrite Rplus_opp_r.
    rewrite Rplus_0_l.
    rewrite <- (Rplus_assoc R1 (-R1)).
    rewrite Rplus_opp_r.
    rewrite Rplus_0_l.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    apply Rlt_0_1.
  }

  intros.

  unfold Rsqr, Rdiv, Rminus.
  repeat (rewrite Rinv_mult_distr).
  repeat (rewrite Rmult_plus_distr_l).
  repeat (rewrite Rmult_plus_distr_r).
  repeat (rewrite Rmult_plus_distr_l).
  repeat (rewrite Rmult_assoc).
  repeat (rewrite Rplus_assoc).
  apply Rplus_eq_compat_l.
  rewrite (Rmult_comm (IZR 4)).
  rewrite (Rmult_comm (/ (IZR 4))).
  repeat (rewrite Rmult_assoc).
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm c).
  repeat (rewrite <- Rmult_assoc).
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite (Rplus_comm c).
  repeat (rewrite <- Rplus_assoc).
  apply Rplus_eq_compat_r.
  repeat (rewrite Rmult_assoc).
  rewrite (Rmult_comm (/ (IZR 2))).
  repeat (rewrite Rmult_assoc).
  pattern b at 1;rewrite (Rmult_comm b).
  repeat (rewrite <- Rmult_assoc).
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  repeat (rewrite Rmult_assoc).
  pattern b at 1;rewrite (Rmult_comm b).
  repeat (rewrite Rmult_assoc).
  pattern x at 2;rewrite (Rmult_comm x).
  repeat (rewrite Rmult_assoc).
  pattern (/ (IZR 2)) at 1;rewrite (Rmult_comm (/ (IZR 2) )).
  repeat (rewrite <- Rmult_assoc).
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  repeat (rewrite <- Rmult_assoc).
  pattern x at 1;rewrite (Rmult_comm x).
  rewrite (Rmult_comm _ (/ (IZR 2))).
  repeat (rewrite Rmult_assoc).
  rewrite <- (Rmult_plus_distr_l (/ (IZR 2))).
  pattern x at 1;rewrite (Rmult_comm x).
  rewrite <- double.
  repeat (rewrite <- Rmult_assoc).
  rewrite Rinv_l.
  rewrite Rmult_1_l.
  repeat rewrite (Rplus_assoc).
  pattern (b*x) at 1;rewrite <- (Rplus_0_r (b*x)).
  apply Rplus_eq_compat_l.
  repeat (rewrite Rmult_assoc).
  rewrite (Rmult_comm (/ (IZR 2))).
  repeat (rewrite Rmult_assoc).
  rewrite (Rmult_comm b).
  repeat (rewrite <- Rmult_assoc).
  rewrite Rinv_r. rewrite Rmult_1_l.
  repeat (rewrite Rmult_assoc).
  rewrite (Rmult_comm (/ (IZR 2))).
  rewrite (Rmult_comm (- (b*b))).
  repeat (rewrite Rmult_assoc).
  rewrite <- (Rmult_plus_distr_l (/a)).
  apply Rmult_eq_reg_l with a.
  rewrite Rmult_0_r.
  repeat (rewrite <- Rmult_assoc).
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite <- Ropp_mult_distr_r.
  repeat (rewrite Rmult_assoc).
  pattern b at 1;rewrite (Rmult_comm b).
  pattern b at 0;rewrite (Rmult_comm b).
  repeat (rewrite <- Rmult_assoc).
  rewrite <- (Rinv_mult_distr).
  change (IZR 2 * IZR 2) with (IZR 4).
  repeat (rewrite Rmult_assoc).
  rewrite Rplus_opp_r.
  reflexivity.

  assumption.
  assumption.

  apply cond_nonzero.
  apply cond_nonzero.
  apply cond_nonzero.

  assumption.

  apply cond_nonzero.
  apply cond_nonzero.
  apply cond_nonzero.

  assumption.
  assumption.
  apply cond_nonzero.
  assumption.
  apply cond_nonzero.

Qed.

Lemma Rsqr_eq : forall x y:R, Rsqr x = Rsqr y -> x = y \/ x = - y.
Proof.
  intros x y h.
  apply (Rplus_eq_compat_r (- (Rsqr y))) in h. 
  rewrite Rplus_opp_r in h.
  fold (Rsqr x - Rsqr y) in h.
  rewrite <- Rsqr_plus_minus in h.
  apply Rmult_integral in h.
  destruct h.
  right. apply Rplus_eq_reg_r with y. rewrite Rplus_opp_l. assumption.
  left. apply Rplus_eq_reg_r with (-y). rewrite Rplus_opp_r. assumption.
Qed.
