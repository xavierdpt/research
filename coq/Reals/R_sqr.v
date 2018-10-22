Require Import Rbase.
Require Import Rbasic_fun.
Local Open Scope R_scope.

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

Lemma Rsqr_plus : forall x y:R, Rsqr (x + y) = Rsqr x + Rsqr y + 2 * x * y.
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

Lemma Rsqr_minus : forall x y:R, Rsqr (x - y) = Rsqr x + Rsqr y - 2 * x * y.
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

Lemma Rsqr_1 : Rsqr 1 = 1.
Proof.
  unfold Rsqr.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma Rsqr_gt_0_0 : forall x:R, 0 < Rsqr x -> x <> 0.
Proof.
  unfold Rsqr.
  intros x h.
  destruct (Rtotal_order x 0) as [ lt | [ eq | gt ]].
  apply Rlt_not_eq. assumption.
  subst x. rewrite Rmult_0_r in h.
  apply Rlt_not_eq. assumption.
  apply Rgt_not_eq. assumption.
Qed.

Lemma Rsqr_pos_lt : forall x:R, x <> 0 -> 0 < Rsqr x.
Proof.
  intros x h.
  unfold Rsqr.
  destruct (Rtotal_order x 0) as [ lt | [ eq | gt ]].
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

Lemma Rsqr_div : forall x y:R, y <> 0 -> Rsqr (x / y) = Rsqr x / Rsqr y.
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

Lemma Rsqr_eq_0 : forall x:R, Rsqr x = 0 -> x = 0.
Proof.
  unfold Rsqr.
  intros x h.
  destruct (Rtotal_order x 0) as [ lt | [ eq | gt ]].
  apply Rmult_eq_reg_r with x. rewrite h. rewrite Rmult_0_l. reflexivity.
  apply Rlt_not_eq. assumption.
  assumption.
  apply Rmult_eq_reg_r with x. rewrite h. rewrite Rmult_0_l. reflexivity.
  apply Rgt_not_eq. assumption.
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
  forall x y:R, Rsqr x <= Rsqr y -> 0 <= x -> 0 <= y -> x <= y.
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
    exfalso. apply Rlt_irrefl with 0. apply Rlt_trans with x.
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
  Search (_ * _< _ * _).
  apply Rmult_le_0_lt_compat.
  left. assumption.
  left. assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma Rsqr_incr_0_var : forall x y:R, Rsqr x <= Rsqr y -> 0 <= y -> x <= y.
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
      exfalso. apply Rlt_irrefl with 0. assumption.
    }
    unfold Rsqr in H0. exfalso. apply Rlt_irrefl with 0. apply Rlt_trans with (x*x);assumption.
  }
  destruct hsqr.
  2:{
    destruct (Rtotal_order x y).
    left. assumption.
    destruct H1. right. assumption.
    exfalso. apply Rlt_irrefl with (x*x).
    pattern (x*x) at 1;rewrite H0.
    Search (_ * _< _ * _).
    apply Rmult_gt_0_lt_compat.
    assumption.
    apply Rgt_trans with y. assumption. assumption.
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
  forall x y:R, x <= y -> 0 <= x -> 0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y hxy hx hy.
  unfold Rsqr.
  apply Rmult_le_compat.
  assumption. assumption. assumption. assumption.
Qed.

Lemma Rsqr_incrst_0 :
  forall x y:R, Rsqr x < Rsqr y -> 0 <= x -> 0 <= y -> x < y.
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
    subst y. exfalso. apply Rlt_irrefl with 0. apply Rlt_trans with x.
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
  forall x y:R, x < y -> 0 <= x -> 0 <= y -> Rsqr x < Rsqr y.
Proof.
  intros x y hxy hx hy.
  unfold Rsqr.
  apply Rmult_le_0_lt_compat.
  assumption. assumption. assumption. assumption.
Qed.

Lemma Rsqr_neg_pos_le_0 :
  forall x y:R, Rsqr x <= Rsqr y -> 0 <= y -> - y <= x.
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
    apply (Rplus_eq_compat_r (-y²)) in heq.
    rewrite Rplus_opp_r in heq.
    fold (x²-y²) in heq.
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
      left. apply Rlt_trans with 0.
      - rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
      - assumption.
    }
  }
  (* We now distinguish between the cases 0 < x, 0 = x and 0 > x *)
  destruct (Rtotal_order 0 x) as [ xpos | [ xnul | xneg ] ].
  { (* 0 < x *)
    left.
    apply Rlt_trans with (-x).
    + apply Ropp_lt_contravar.
      apply Rsqr_incrst_0.
      - assumption.
      - left. assumption.
      - left. assumption.
    + apply Rlt_trans with 0.
      - rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
      - assumption.
  }
  { (* 0 = x *)
    subst x. left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
  }
  {
    left.
    apply Rgt_lt in xneg.
    rewrite <- Ropp_involutive with x.
    apply Ropp_lt_contravar.
    apply Rsqr_incrst_0.
    + rewrite <- Rsqr_neg. assumption.
    + left. rewrite <- Ropp_0. apply Ropp_lt_contravar. assumption.
    + left. assumption.
  }
Qed.

Lemma Rsqr_neg_pos_le_1 :
  forall x y:R, - y <= x -> x <= y -> 0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y H H0 H1; destruct (Rcase_abs x) as [Hlt|Hle].
  apply Ropp_lt_gt_contravar, Rlt_le in Hlt; rewrite Ropp_0 in Hlt;
  apply Ropp_le_ge_contravar, Rge_le in H; rewrite Ropp_involutive in H;
  rewrite (Rsqr_neg x); apply Rsqr_incr_1; assumption.
  apply Rge_le in Hle; apply Rsqr_incr_1; assumption.
Qed.

Lemma neg_pos_Rsqr_le : forall x y:R, - y <= x -> x <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y H H0; destruct (Rcase_abs x) as [Hlt|Hle].
  apply Ropp_lt_gt_contravar, Rlt_le in Hlt; rewrite Ropp_0 in Hlt;
  apply Ropp_le_ge_contravar, Rge_le in H; rewrite Ropp_involutive in H.
  assert (0 <= y) by (apply Rle_trans with (-x); assumption).
  rewrite (Rsqr_neg x); apply Rsqr_incr_1; assumption.
  apply Rge_le in Hle;
  assert (0 <= y) by (apply Rle_trans with x; assumption).
  apply Rsqr_incr_1; assumption.
Qed.

Lemma Rsqr_abs : forall x:R, Rsqr x = Rsqr (Rabs x).
Proof.
  intro; unfold Rabs; case (Rcase_abs x); intro;
    [ apply Rsqr_neg | reflexivity ].
Qed.

Lemma Rsqr_le_abs_0 : forall x y:R, Rsqr x <= Rsqr y -> Rabs x <= Rabs y.
Proof.
  intros; apply Rsqr_incr_0; repeat rewrite <- Rsqr_abs;
    [ assumption | apply Rabs_pos | apply Rabs_pos ].
Qed.

Lemma Rsqr_le_abs_1 : forall x y:R, Rabs x <= Rabs y -> Rsqr x <= Rsqr y.
Proof.
  intros; rewrite (Rsqr_abs x); rewrite (Rsqr_abs y);
    apply (Rsqr_incr_1 (Rabs x) (Rabs y) H (Rabs_pos x) (Rabs_pos y)).
Qed.

Lemma Rsqr_lt_abs_0 : forall x y:R, Rsqr x < Rsqr y -> Rabs x < Rabs y.
Proof.
  intros; apply Rsqr_incrst_0; repeat rewrite <- Rsqr_abs;
    [ assumption | apply Rabs_pos | apply Rabs_pos ].
Qed.

Lemma Rsqr_lt_abs_1 : forall x y:R, Rabs x < Rabs y -> Rsqr x < Rsqr y.
Proof.
  intros; rewrite (Rsqr_abs x); rewrite (Rsqr_abs y);
    apply (Rsqr_incrst_1 (Rabs x) (Rabs y) H (Rabs_pos x) (Rabs_pos y)).
Qed.

Lemma Rsqr_inj : forall x y:R, 0 <= x -> 0 <= y -> Rsqr x = Rsqr y -> x = y.
Proof.
  intros; generalize (Rle_le_eq (Rsqr x) (Rsqr y)); intro; elim H2; intros _ H3;
    generalize (H3 H1); intro; elim H4; intros; apply Rle_antisym;
      apply Rsqr_incr_0; assumption.
Qed.

Lemma Rsqr_eq_abs_0 : forall x y:R, Rsqr x = Rsqr y -> Rabs x = Rabs y.
Proof.
  intros; unfold Rabs; case (Rcase_abs x) as [Hltx|Hgex];
    case (Rcase_abs y) as [Hlty|Hgey].
  rewrite (Rsqr_neg x), (Rsqr_neg y) in H;
    generalize (Ropp_lt_gt_contravar y 0 Hlty);
      generalize (Ropp_lt_gt_contravar x 0 Hltx); rewrite Ropp_0;
        intros; generalize (Rlt_le 0 (- x) H0); generalize (Rlt_le 0 (- y) H1);
          intros; apply Rsqr_inj; assumption.
  rewrite (Rsqr_neg x) in H; generalize (Rge_le y 0 Hgey); intro;
    generalize (Ropp_lt_gt_contravar x 0 Hltx); rewrite Ropp_0;
      intro; generalize (Rlt_le 0 (- x) H1); intro; apply Rsqr_inj;
        assumption.
  rewrite (Rsqr_neg y) in H; generalize (Rge_le x 0 Hgex); intro;
    generalize (Ropp_lt_gt_contravar y 0 Hlty); rewrite Ropp_0;
      intro; generalize (Rlt_le 0 (- y) H1); intro; apply Rsqr_inj;
        assumption.
  apply Rsqr_inj; auto using Rge_le.
Qed.

Lemma Rsqr_eq_asb_1 : forall x y:R, Rabs x = Rabs y -> Rsqr x = Rsqr y.
Proof.
  intros; cut (Rsqr (Rabs x) = Rsqr (Rabs y)).
  intro; repeat rewrite <- Rsqr_abs in H0; assumption.
  rewrite H; reflexivity.
Qed.

Lemma triangle_rectangle :
  forall x y z:R,
    0 <= z -> Rsqr x + Rsqr y <= Rsqr z -> - z <= x <= z /\ - z <= y <= z.
Proof.
  intros;
    generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (Rle_0_sqr y) H0);
      rewrite Rplus_comm in H0;
        generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (Rle_0_sqr x) H0);
          intros; split;
            [ split;
              [ apply Rsqr_neg_pos_le_0; assumption
                | apply Rsqr_incr_0_var; assumption ]
              | split;
                [ apply Rsqr_neg_pos_le_0; assumption
                  | apply Rsqr_incr_0_var; assumption ] ].
Qed.

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

Lemma Rsqr_inv : forall x:R, x <> 0 -> Rsqr (/ x) = / Rsqr x.
Proof.
  intros; unfold Rsqr.
  rewrite Rinv_mult_distr; try reflexivity || assumption.
Qed.

Lemma canonical_Rsqr :
  forall (a:nonzeroreal) (b c x:R),
    a * Rsqr x + b * x + c =
    a * Rsqr (x + b / (2 * a)) + (4 * a * c - Rsqr b) / (4 * a).
Proof.
  intros.
  unfold Rsqr.
  field.
  apply a.
Qed.

Lemma Rsqr_eq : forall x y:R, Rsqr x = Rsqr y -> x = y \/ x = - y.
Proof.
  intros; unfold Rsqr in H;
    generalize (Rplus_eq_compat_l (- (y * y)) (x * x) (y * y) H);
      rewrite Rplus_opp_l; replace (- (y * y) + x * x) with ((x - y) * (x + y)).
  intro; generalize (Rmult_integral (x - y) (x + y) H0); intro; elim H1; intros.
  left; apply Rminus_diag_uniq; assumption.
  right; apply Rminus_diag_uniq; unfold Rminus; rewrite Ropp_involutive;
    assumption.
  ring.
Qed.
