(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import XRbase.
Require Import XRanalysis_reg.
Require Import XRfunctions.
Require Import XRseries.
Require Import XRiemannInt.
Require Import XSeqProp.
Require Import Max.
Require Import Omega.
Local Open Scope XR_scope.

(** * Preliminaries lemmas *)

Lemma f_incr_implies_g_incr_interv : forall f g:R->R, forall lb ub,
       lb < ub ->
       (forall x y, lb <= x -> x < y -> y <= ub -> f x < f y) ->
       (forall x, f lb <= x -> x <= f ub -> (comp f g) x = id x) ->
       (forall x , f lb <= x -> x <= f ub -> lb <= g x <= ub) ->
       (forall x y, f lb <= x -> x < y -> y <= f ub -> g x < g y).
Proof.
  intros f g lb ub lb_lt_ub f_incr f_eq_g g_ok x y lb_le_x x_lt_y y_le_ub.
  assert (x_encad : f lb <= x <= f ub).
{
split. assumption.
eapply Rle_trans with y.
left. assumption.
assumption.
}
  assert (y_encad : f lb <= y <= f ub). {
split.
apply Rle_trans with x.
assumption.
left. assumption.
assumption.
}
  assert (gx_encad := g_ok _ (proj1 x_encad) (proj2 x_encad)).
  assert (gy_encad := g_ok _ (proj1 y_encad) (proj2 y_encad)).
  case (Rlt_dec (g x) (g y)); [ easy |].
  intros Hfalse.
  assert (Temp := Rnot_lt_le _ _ Hfalse).
{
  enough (y <= x). {
exfalso. eapply Rlt_irrefl. eapply Rlt_le_trans.
exact x_lt_y. assumption.
}
  replace y with (id y) by easy.
  replace x with (id x) by easy.
  rewrite <- f_eq_g by easy.
  rewrite <- f_eq_g by easy.
  assert (f_incr2 : forall x y, lb <= x -> x <= y -> y < ub -> f x <= f y).
 {
    intros m n lb_le_m m_le_n n_lt_ub.
    case (m_le_n).
{
    - intros; apply Rlt_le, f_incr, Rlt_le; assumption.
}
{
    - intros Hyp; rewrite Hyp; apply Req_le; reflexivity.
}
  }
  apply f_incr2; intuition.
  enough (g x <> ub). {
clear H6 H5 H3 H2 H1 H0.
destruct H4. assumption.
subst ub. destruct H7. reflexivity.
}
  intro Hf.
  assert (Htemp : (comp f g) x = f ub). {
    unfold comp; rewrite Hf; reflexivity.
  }
  rewrite f_eq_g in Htemp by easy.
  unfold id in Htemp.
clear H0.
eapply Rlt_irrefl.
eapply Rlt_le_trans.
exact x_lt_y.
eapply Rle_trans.
apply y_le_ub.
right. symmetry. assumption.

}
Qed.

Lemma derivable_pt_id_interv : forall (lb ub x:R),
       lb <= x <= ub ->
       derivable_pt id x.
Proof.
intros.
 reg.
Qed.

Lemma pr_nu_var2_interv : forall (f g : R -> R) (lb ub x : R) (pr1 : derivable_pt f x)
       (pr2 : derivable_pt g x),
       lb < ub ->
       lb < x < ub ->
       (forall h : R, lb < h < ub -> f h = g h) -> derive_pt f x pr1 = derive_pt g x pr2.
Proof.
intros f g lb ub x Prf Prg lb_lt_ub x_encad local_eq.
assert (forall x l, lb < x < ub -> (derivable_pt_abs f x l <-> derivable_pt_abs g x l)).
 intros a l a_encad.
 unfold derivable_pt_abs, derivable_pt_lim.
 split.
 intros Hyp eps eps_pos.
 elim (Hyp eps eps_pos) ; intros delta Hyp2.
 assert (Pos_cond : R0 < Rmin delta (Rmin (ub - a) (a - lb)) ).
  clear-a lb ub a_encad delta.
  apply Rmin_pos ; [exact (delta.(cond_pos)) | apply Rmin_pos ] ; apply Rlt_Rminus ; intuition.
 exists (mkposreal (Rmin delta (Rmin (ub - a) (a - lb))) Pos_cond).
 intros h h_neq h_encad.
 replace (g (a + h) - g a) with (f (a + h) - f a).
 apply Hyp2 ; intuition.
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))).
 assumption. apply Rmin_l.
 assert (local_eq2 : forall h : R, lb < h < ub -> - f h = - g h).
  intros ; apply Ropp_eq_compat ; intuition.
 rewrite local_eq ; unfold Rminus. rewrite local_eq2. reflexivity.
 assumption.
 assert (Sublemma2 : forall x y, Rabs x < Rabs y -> R0 < y -> x < y).
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
 split.
 assert (Sublemma : forall x y z, -z < y - x -> x < y + z).
  intros.
{
eapply Rplus_lt_reg_r.
rewrite Rplus_opp_r.
rewrite Rplus_assoc.
rewrite Rplus_comm.
apply Rplus_lt_reg_l with (-z).
rewrite Rplus_0_r.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
rewrite Rplus_comm.
assumption.
}
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros.
{
  apply Rplus_lt_reg_l with (-x0).
rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
rewrite Rplus_comm. assumption.
}
 apply Sublemma.
 apply Sublemma2.
 apply Rlt_le_trans with (r2:=ub-a) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 intros Hyp eps eps_pos.
 elim (Hyp eps eps_pos) ; intros delta Hyp2.
 assert (Pos_cond : R0 < Rmin delta (Rmin (ub - a) (a - lb)) ).
  clear-a lb ub a_encad delta.
  apply Rmin_pos ; [exact (delta.(cond_pos)) | apply Rmin_pos ] ; apply Rlt_Rminus ; intuition.
 exists (mkposreal (Rmin delta (Rmin (ub - a) (a - lb))) Pos_cond).
 intros h h_neq h_encad.
 replace (f (a + h) - f a) with (g (a + h) - g a).
 apply Hyp2 ; intuition.
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))).
 assumption. apply Rmin_l.
 assert (local_eq2 : forall h : R, lb < h < ub -> - f h = - g h).
  intros ; apply Ropp_eq_compat ; intuition.
 rewrite local_eq ; unfold Rminus. rewrite local_eq2. reflexivity.
 assumption.
 assert (Sublemma2 : forall x y, Rabs x < Rabs y -> R0 < y -> x < y).
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
   apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
   apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
 split.
 assert (Sublemma : forall x y z, -z < y - x -> x < y + z).
  intros.
{
apply Rplus_lt_reg_r with (-x0).
rewrite Rplus_opp_r.
apply Rplus_lt_reg_l with (-z).
rewrite Rplus_0_r.
rewrite (Rplus_comm y).
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
assumption.
}
 apply Sublemma.
 apply Sublemma2. rewrite Rabs_Ropp.
 apply Rlt_le_trans with (r2:=a-lb) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_r] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 assert (Sublemma : forall x y z, y < z - x -> x + y < z).
  intros.
{
apply Rplus_lt_reg_r with (-x0).
rewrite (Rplus_comm x0).
rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
assumption.
}
 apply Sublemma.
 apply Sublemma2.
 apply Rlt_le_trans with (r2:=ub-a) ; [| apply RRle_abs] ;
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 apply Rlt_le_trans with (r2:=Rmin (ub - a) (a - lb)) ; [| apply Rmin_l] ;
 apply Rlt_le_trans with (r2:=Rmin delta (Rmin (ub - a) (a - lb))) ; [| apply Rmin_r] ; assumption.
 unfold derivable_pt in Prf.
  unfold derivable_pt in Prg.
  elim Prf; intros x0 p.
  elim Prg; intros x1 p0.
  assert (Temp := p); rewrite H in Temp.
  unfold derivable_pt_abs in p.
  unfold derivable_pt_abs in p0.
  simpl in |- *.
  apply (uniqueness_limite g x x0 x1 Temp p0).
  assumption.
Qed.


(* begin hide *)
Lemma leftinv_is_rightinv : forall (f g:R->R),
       (forall x y, x < y -> f x < f y) ->
       (forall x, (comp f g) x = id x) ->
       (forall x, (comp g f) x = id x).
Proof.
intros f g f_incr Hyp x.
 assert (forall x, f (g (f x)) = f x).
  intros ; apply Hyp.
 assert(f_inj : forall x y, f x = f y -> x = y).
  intros a b fa_eq_fb.
  case(total_order_T a b).
  intro s ; case s ; clear s.
  intro Hf.
  assert (Hfalse := f_incr a b Hf).
  apply False_ind. apply (Rlt_not_eq (f a) (f b)) ; assumption.
  intuition.
  intro Hf. assert (Hfalse := f_incr b a Hf).
  apply False_ind. apply (Rlt_not_eq (f b) (f a)) ; [|symmetry] ; assumption.
 apply f_inj. unfold comp.
 unfold comp in Hyp.
 rewrite Hyp.
 unfold id.
 reflexivity.
Qed.
(* end hide *)

Lemma leftinv_is_rightinv_interv : forall (f g:R->R) (lb ub:R),
       (forall x y, lb <= x -> x < y -> y <= ub -> f x < f y) ->
       (forall y, f lb <= y -> y <= f ub -> (comp f g) y = id y) ->
       (forall x, f lb <= x -> x <= f ub -> lb <= g x <= ub) ->
       forall x,
       lb <= x <= ub ->
       (comp g f) x = id x.
Proof.
intros f g lb ub f_incr_interv Hyp g_wf x x_encad.
 assert(f_inj : forall x y, lb <= x <= ub -> lb <= y <= ub -> f x = f y -> x = y).
  intros a b a_encad b_encad fa_eq_fb.
  case(total_order_T a b).
  intro s ; case s ; clear s.
  intro Hf.
  assert (Hfalse := f_incr_interv a b (proj1 a_encad) Hf (proj2 b_encad)).
  apply False_ind. apply (Rlt_not_eq (f a) (f b)) ; assumption.
  intuition.
  intro Hf. assert (Hfalse := f_incr_interv b a (proj1 b_encad) Hf (proj2 a_encad)).
  apply False_ind. apply (Rlt_not_eq (f b) (f a)) ; [|symmetry] ; assumption.
 assert (f_incr_interv2 : forall x y, lb <= x -> x <= y -> y <= ub -> f x <= f y).
  intros m n cond1 cond2 cond3.
   case cond2.
   intro cond. apply Rlt_le ; apply f_incr_interv ; assumption.
   intro cond ; right ; rewrite cond ; reflexivity.
 assert (Hyp2:forall x, lb <= x <= ub -> f (g (f x)) = f x).
  intros ; apply Hyp.  apply f_incr_interv2 ; intuition. 
 apply f_incr_interv2 ; intuition.
 unfold comp ; unfold comp in Hyp.
 apply f_inj.
 apply g_wf ; apply f_incr_interv2 ; intuition.
 unfold id ; assumption.
 apply Hyp2 ; unfold id ; assumption.
Qed.


(** Intermediate Value Theorem on an Interval (Proof mainly taken from Reals.Rsqrt_def) and its corollary *)

Lemma IVT_interv_prelim0 : forall (x y:R) (P:R->bool) (N:nat),
       x < y ->
       x <= Dichotomy_ub x y P N <= y /\ x <= Dichotomy_lb x y P N <= y.
Proof.
assert (Sublemma : forall x y lb ub, lb <= x <= ub /\ lb <= y <= ub -> lb <= (x+y) / R2 <= ub).
  intros x y lb ub Hyp.
{
destruct Hyp.
destruct H, H0.
split.
pattern lb;rewrite <- Rmult_1_r.
rewrite <- (Rinv_l R2).
rewrite <- Rmult_assoc.
rewrite Rmult_comm.
rewrite double.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
apply Rmult_le_compat_r.
left. apply Rinv_0_lt_compat. exact Rlt_0_2.
assumption.
apply Rmult_le_compat_r.
left. apply Rinv_0_lt_compat. exact Rlt_0_2.
assumption.
exact Neq_2_0.

pattern ub;rewrite <- Rmult_1_r.
rewrite <- (Rinv_l R2).
rewrite <- Rmult_assoc.
rewrite Rmult_comm.
rewrite double.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
apply Rmult_le_compat_r.
left. apply Rinv_0_lt_compat. exact Rlt_0_2.
assumption.
apply Rmult_le_compat_r.
left. apply Rinv_0_lt_compat. exact Rlt_0_2.
assumption.
exact Neq_2_0.
}
intros x y P N x_lt_y.
induction N.
 simpl ; intuition.
 simpl.
 case (P ((Dichotomy_lb x y P N + Dichotomy_ub x y P N) / R2)).
 split. apply Sublemma ; intuition.
 intuition.
 split. intuition.
 apply Sublemma ; intuition.
Qed.

Lemma IVT_interv_prelim1 : forall (x y x0:R) (D : R -> bool),
       x < y ->
       Un_cv (dicho_up x y D) x0 ->
       x <= x0 <= y.
Proof.
intros x y x0 D x_lt_y bnd.
 assert (Main : forall n, x <= dicho_up x y D n <= y).
  intro n. unfold dicho_up.
  apply (proj1 (IVT_interv_prelim0 x y D n x_lt_y)).
 split.
  apply Rle_cv_lim with (Vn:=dicho_up x y D) (Un:=fun n => x).
  intro n ; exact (proj1 (Main n)).
  unfold Un_cv ; intros ; exists 0%nat ; intros ; unfold R_dist ; replace (x -x) with R0 . rewrite Rabs_R0 ; assumption.
unfold Rminus. rewrite Rplus_opp_r. reflexivity.
  assumption.
  apply Rle_cv_lim with (Un:=dicho_up x y D) (Vn:=fun n => y).
  intro n ; exact (proj2 (Main n)).
  assumption.
  unfold Un_cv ; intros ; exists 0%nat ; intros ; unfold R_dist ; replace (y -y) with R0. rewrite Rabs_R0 ; assumption.
unfold Rminus. rewrite Rplus_opp_r. reflexivity.
Qed.

Lemma IVT_interv : forall (f : R -> R) (x y : R),
       (forall a, x <= a <= y -> continuity_pt f a) ->
       x < y ->
       f x < R0 ->
       R0 < f y ->
       {z : R | x <= z <= y /\ f z = R0}.
Proof.
intros. (* f x y f_cont_interv x_lt_y fx_neg fy_pos.*)
  cut (x <= y).
  intro.
  generalize (dicho_lb_cv x y (fun z:R => cond_positivity (f z)) H3). 
  generalize (dicho_up_cv x y (fun z:R => cond_positivity (f z)) H3). 
  intros X X0.
  elim X; intros x0 p.
  elim X0; intros x1 p0.
  assert (H4 := cv_dicho _ _ _ _ _ H3 p0 p).
  rewrite H4 in p0.
  exists x0.
  split.
  split.
  apply Rle_trans with (dicho_lb x y (fun z:R => cond_positivity (f z)) 0).
  simpl in |- *.
  right; reflexivity.
  apply growing_ineq.
  apply dicho_lb_growing; assumption.
  assumption.
  apply Rle_trans with (dicho_up x y (fun z:R => cond_positivity (f z)) 0).
  apply decreasing_ineq.
  apply dicho_up_decreasing; assumption.
  assumption.
  right; reflexivity.
  2: left; assumption.
  set (Vn := fun n:nat => dicho_lb x y (fun z:R => cond_positivity (f z)) n).
  set (Wn := fun n:nat => dicho_up x y (fun z:R => cond_positivity (f z)) n).
  cut ((forall n:nat, f (Vn n) <= R0) -> f x0 <= R0).
  cut ((forall n:nat, R0 <= f (Wn n)) -> R0 <= f x0).
  intros.
  cut (forall n:nat, f (Vn n) <= R0).
  cut (forall n:nat, R0 <= f (Wn n)).
  intros.
  assert (H9 := H6 H8).
  assert (H10 := H5 H7).
  apply Rle_antisym; assumption.
  intro.
  unfold Wn in |- *.
  cut (forall z:R, cond_positivity z = true <-> R0 <= z).
  intro.
  assert (H8 := dicho_up_car x y (fun z:R => cond_positivity (f z)) n).
  elim (H7 (f (dicho_up x y (fun z:R => cond_positivity (f z)) n))); intros.
  apply H9.
  apply H8.
  elim (H7 (f y)); intros.
  apply H12.
  left; assumption.
  intro.
  unfold cond_positivity in |- *.
  destruct (Rle_dec R0 z) as [|Hnotle].
  split.
  intro; assumption.
  intro; reflexivity.
  split.
  intro feqt;discriminate feqt.
  intro.
  elim Hnotle; assumption.
  unfold Vn in |- *.
  cut (forall z:R, cond_positivity z = false <-> z < R0).
  intros.
  assert (H8 := dicho_lb_car x y (fun z:R => cond_positivity (f z)) n).
  left.
  elim (H7 (f (dicho_lb x y (fun z:R => cond_positivity (f z)) n))); intros.
  apply H9.
  apply H8.
  elim (H7 (f x)); intros.
  apply H12.
  assumption.
  intro.
  unfold cond_positivity in |- *.
  destruct (Rle_dec R0 z) as [Hle|].
  split.
  intro feqt; discriminate feqt.
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle H7)).
  split.
  intro; auto with real.
  intro; reflexivity.
  cut (Un_cv Wn x0).
  intros.
  assert (Temp : x <= x0 <= y).
   apply IVT_interv_prelim1 with (D:=(fun z : R => cond_positivity (f z))) ; assumption.
  assert (H7 := continuity_seq f Wn x0 (H x0 Temp) H5).
  destruct (total_order_T R0 (f x0)) as [[Hlt|<-]|Hgt].
  left; assumption.
  right; reflexivity.
  unfold Un_cv in H7; unfold R_dist in H7.
  cut (R0 < - f x0).
  intro.
  elim (H7 (- f x0) H8); intros.
  cut (x2 >= x2)%nat; [ intro | unfold ge in |- *; apply le_n ].
  assert (H11 := H9 x2 H10).
  rewrite Rabs_right in H11.
  pattern (- f x0) at 1 in H11; rewrite <- Rplus_0_r in H11.
  unfold Rminus in H11; rewrite (Rplus_comm (f (Wn x2))) in H11.
  assert (H12 := Rplus_lt_reg_l _ _ _ H11).
  assert (H13 := H6 x2).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H13 H12)).
  apply Rle_ge; left; unfold Rminus in |- *; apply Rplus_le_lt_0_compat.
  apply H6.
  exact H8.
  apply Ropp_0_gt_lt_contravar; assumption.
  unfold Wn in |- *; assumption.
  cut (Un_cv Vn x0).
  intros.
  assert (Temp : x <= x0 <= y).
   apply IVT_interv_prelim1 with (D:=(fun z : R => cond_positivity (f z))) ; assumption.
  assert (H7 := continuity_seq f Vn x0 (H x0 Temp) H5).
  destruct (total_order_T R0 (f x0)) as [[Hlt|Heq]|].
  unfold Un_cv in H7; unfold R_dist in H7.
  elim (H7 (f x0) Hlt); intros.
  cut (x2 >= x2)%nat; [ intro | unfold ge; apply le_n ].
  assert (H10 := H8 x2 H9).
  rewrite Rabs_left in H10.
  pattern (f x0) at 2 in H10; rewrite <- Rplus_0_r in H10.
  rewrite Ropp_minus_distr' in H10.
  unfold Rminus in H10.
  assert (H11 := Rplus_lt_reg_l _ _ _ H10).
  assert (H12 := H6 x2).
  cut (R0 < f (Vn x2)).
  intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H13 H12)).
  rewrite <- (Ropp_involutive (f (Vn x2))).
  apply Ropp_0_gt_lt_contravar; assumption.
  apply Rplus_lt_reg_l with (f x0 - f (Vn x2)).
  rewrite Rplus_0_r; replace (f x0 - f (Vn x2) + (f (Vn x2) - f x0)) with R0;
    [ unfold Rminus in |- *; apply Rplus_lt_le_0_compat | idtac ].
  assumption.
  rewrite <- Ropp_0.
  apply Ropp_le_contravar; apply Rle_ge; apply H6.
unfold Rminus. rewrite Rplus_assoc, Rplus_comm.
repeat rewrite Rplus_assoc. rewrite Rplus_opp_l, Rplus_0_r.
rewrite Rplus_opp_l. reflexivity.
  right; rewrite <- Heq; reflexivity.
  left; assumption.
  unfold Vn in |- *; assumption.
Qed.

Lemma f_interv_is_interv : forall (f:R->R) (lb ub y:R),
       lb < ub ->
       f lb <= y <= f ub ->
       (forall x, lb <=  x <= ub -> continuity_pt f x) ->
       {x | lb <= x <= ub /\ f x = y}.
Proof.
  intros f lb ub y lb_lt_ub y_encad f_cont_interv.
  case y_encad.
  intro y_encad1.
  destruct (total_order_T (f lb) y) as [ [ lala | lala ] | lala ].
  3:{ exfalso. eapply Rlt_irrefl. eapply Rlt_le_trans. exact lala. assumption. }
  {
    generalize dependent lala.
    intros y_encad2 y_encad3.
    destruct (total_order_T y (f ub)) as [ [ lala | lala ] | lala ].
    3:{ exfalso. eapply Rlt_irrefl. eapply Rlt_le_trans. exact lala. assumption. }
    {
      generalize dependent lala.
      intro y_encad4.
      clear y_encad y_encad1 y_encad3.
      assert (Cont : forall a : R, lb <= a <= ub -> continuity_pt (fun x => f x - y) a).
      {
        intros a a_encad.
        unfold continuity_pt, continue_in, limit1_in, limit_in.
        simpl.
        unfold R_dist.
        intros eps eps_pos.
        elim (f_cont_interv a a_encad eps eps_pos).
        intros alpha alpha_pos.
        destruct alpha_pos as (alpha_pos,Temp).
        exists alpha.
        split.
        { assumption. }
        {
          intros x x_cond.
          replace (f x - y - (f a - y)) with (f x - f a).
          exact (Temp x x_cond).
          unfold Rminus.
          rewrite Ropp_plus_distr.
          rewrite Ropp_involutive.
          repeat rewrite Rplus_assoc.
          apply Rplus_eq_compat_l.
          rewrite Rplus_comm.
          rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
          reflexivity.
        }
      }

      assert (H1 : (fun x : R => f x - y) lb < R0).
      {
        apply Rlt_minus.
        assumption.
      }

      assert (H2 : R0 < (fun x : R => f x - y) ub).
      {
        apply Rgt_minus.
        assumption.
      }

      destruct (IVT_interv (fun x => f x - y) lb ub Cont lb_lt_ub H1 H2) as (x,Hx).
      exists x.
      destruct Hx as (lb_x_ub, eq).
      split.
      assumption.
      apply Rplus_eq_reg_r with (-y).
      rewrite Rplus_opp_r.
      assumption.
    }
    {
      generalize dependent lala.
      intro eq.
      exists ub.
      split.
      split.
      left;assumption.
      right;reflexivity.
      symmetry;assumption.
    }
  }
  {
    generalize dependent lala.
    intros eq y_le_fub.
    exists lb.
    split.
    split.
    right;reflexivity.
    left;assumption.
    assumption.
  }
Qed.

(** ** The derivative of a reciprocal function       *)


(** * Continuity of the reciprocal function *)

Lemma continuity_pt_recip_prelim : forall (f g:R->R) (lb ub : R) (Pr1:lb < ub),
       (forall x y, lb <= x -> x < y -> y <= ub -> f x < f y) ->
       (forall x, lb <= x <= ub -> (comp g f) x = id x) ->
       (forall a, lb <= a <= ub -> continuity_pt f a) ->
       forall b,
       f lb < b < f ub ->
       continuity_pt g b.
Proof.
assert (Sublemma : forall x y z, Rmax x y < z <-> x < z /\ y < z).
 intros x y z. split.
  unfold Rmax. case (Rle_dec x y) ; intros Hyp Hyp2.
  split. apply Rle_lt_trans with (r2:=y) ; assumption. assumption.
  split. assumption. apply Rlt_trans with (r2:=x).
  assert (Temp : forall x y, ~ x <= y -> y < x).
   intros m n Hypmn. intuition.
  apply Temp ; clear Temp ; assumption.
  assumption.
  intros Hyp.
  unfold Rmax. case (Rle_dec x y).
  intro ; exact (proj2 Hyp).
  intro ; exact (proj1 Hyp).
assert (Sublemma2 : forall x y z, z < Rmin x y <-> z < x /\ z < y).
 intros x y z. split.
  unfold Rmin. case (Rle_dec x y) ; intros Hyp Hyp2.
  split. assumption.
  apply Rlt_le_trans with (r2:=x) ; intuition.
  split.
  apply Rlt_trans with (r2:=y). intuition.
  assert (Temp : forall x y, ~ x <= y -> y < x).
   intros m n Hypmn. intuition.
  apply Temp ; clear Temp ; assumption.
  assumption.
  intros Hyp.
  unfold Rmin. case (Rle_dec x y).
  intro ; exact (proj1 Hyp).
  intro ; exact (proj2 Hyp).
assert (Sublemma3 : forall x y, x <= y /\ x <> y -> x < y).
 intros m n Hyp. unfold Rle in Hyp.
  destruct Hyp as (Hyp1,Hyp2).
  case Hyp1.
  intuition.
  intro Hfalse ; apply False_ind ; apply Hyp2 ; exact Hfalse.
intros f g lb ub lb_lt_ub f_incr_interv f_eq_g f_cont_interv b b_encad.
 assert (f_incr_interv2 : forall x y, lb <= x -> x <= y -> y <= ub -> f x <= f y).
  intros m n cond1 cond2 cond3.
   case cond2.
   intro cond. apply Rlt_le ; apply f_incr_interv ; assumption.
   intro cond ; right ; rewrite cond ; reflexivity.
 unfold continuity_pt, continue_in, limit1_in, limit_in ; intros eps eps_pos.
 unfold dist ; simpl ; unfold R_dist.
 assert (b_encad_e : f lb <= b <= f ub) by intuition.
 elim (f_interv_is_interv f lb ub b lb_lt_ub b_encad_e f_cont_interv) ; intros x Temp.
 destruct Temp as (x_encad,f_x_b).
 assert (lb_lt_x : lb < x).
 assert (Temp : x <> lb).
  intro Hfalse.
  assert (Temp' : b = f lb).
   rewrite <- f_x_b ; rewrite Hfalse ; reflexivity.
  assert (Temp'' : b <> f lb).
   apply Rgt_not_eq ; exact (proj1 b_encad).
  apply Temp'' ; exact Temp'.
 apply Sublemma3.
 split. exact (proj1 x_encad).
 assert (Temp2 : forall x y:R, x <> y <-> y <> x).
  intros m n. split ; intuition.
 rewrite Temp2 ; assumption.
 assert (x_lt_ub : x < ub).
 assert (Temp : x <> ub).
  intro Hfalse.
  assert (Temp' : b = f ub).
   rewrite <- f_x_b ; rewrite Hfalse ; reflexivity.
  assert (Temp'' : b <> f ub).
   apply Rlt_not_eq ; exact (proj2 b_encad).
  apply Temp'' ; exact Temp'.
 apply Sublemma3.
 split ; [exact (proj2 x_encad) | assumption].
 pose (x1 := Rmax (x - eps) lb).
 pose (x2 := Rmin (x + eps) ub).
 assert (Hx1 : x1 = Rmax (x - eps) lb) by intuition.
 assert (Hx2 : x2 = Rmin (x + eps) ub) by intuition.
 assert (x1_encad : lb <= x1 <= ub).
  split. apply RmaxLess2.
  apply Rlt_le. rewrite Hx1. rewrite Sublemma.
  split. {
apply Rlt_trans with (r2:=x).
unfold Rminus.
rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
assumption.
assumption.
}
  assumption.
 assert (x2_encad : lb <= x2 <= ub).
  split. apply Rlt_le ; rewrite Hx2 ; rewrite Sublemma2.
  split.
{
apply Rlt_trans with (r2:=x).
2:{
pattern x at 1;rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
assumption.
}
assumption.
}
  assumption.
  apply Rmin_r.
 assert (x_lt_x2 : x < x2).
  rewrite Hx2.
  rewrite Sublemma2.
{
  split.
  pattern x at 1;rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  assumption.
  assumption.
}
 assert (x1_lt_x : x1 < x).
  rewrite Hx1.
  rewrite Sublemma.
{
  split.
  unfold Rminus.
  rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  assumption.
  assumption.
}
 exists (Rmin (f x - f x1) (f x2 - f x)).
 split. apply Rmin_pos ; apply Rgt_minus.
{
apply f_incr_interv ; [apply RmaxLess2 | | ].
assumption.
left;assumption.
}
 apply f_incr_interv ; intuition.
 intros y Temp.
 destruct Temp as (_,y_cond).
  rewrite <- f_x_b in y_cond.
  assert (Temp : forall x y d1 d2, R0 < d1 -> R0 < d2 -> Rabs (y - x) < Rmin d1 d2 -> x - d1 <= y <= x + d2).
   intros.
    split. assert (H10 : forall x y z, x - y <= z -> x - z <= y). intuition.
{
unfold Rminus.
apply Rplus_le_reg_r with z.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
apply Rplus_le_reg_l with (-y1).
rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
rewrite Rplus_comm.
assumption.
}
    apply H10. apply Rle_trans with (r2:=Rabs (y0 - x0)).
    replace (Rabs (y0 - x0)) with (Rabs (x0 - y0)). apply RRle_abs.
    rewrite <- Rabs_Ropp. unfold Rminus ; rewrite Ropp_plus_distr. rewrite Ropp_involutive.
    intuition.
    apply Rle_trans with (r2:= Rmin d1 d2). apply Rlt_le ; assumption.
    apply Rmin_l.
    assert (H10 : forall x y z, x - y <= z -> x <= y + z). intuition.
{
apply Rplus_le_reg_l with (-y1).
rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
rewrite Rplus_comm.
assumption.
}
    apply H10. apply Rle_trans with (r2:=Rabs (y0 - x0)). apply RRle_abs.
    apply Rle_trans with (r2:= Rmin d1 d2). apply Rlt_le ; assumption.
    apply Rmin_r.
  assert (Temp' := Temp (f x) y (f x - f x1) (f x2 - f x)).
  replace (f x - (f x - f x1)) with (f x1) in Temp'.
2:{
  unfold Rminus.
  rewrite Ropp_plus_distr, Ropp_involutive.
  rewrite <- Rplus_assoc, Rplus_opp_r, Rplus_0_l.
  reflexivity.
}
  replace (f x + (f x2 - f x)) with (f x2) in Temp'.
2:{
unfold Rminus.
rewrite Rplus_comm.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
reflexivity.
}
  assert (T : R0 < f x - f x1).
   apply Rgt_minus. apply f_incr_interv ; intuition.
  assert (T' : R0 < f x2 - f x ).
   apply Rgt_minus. apply f_incr_interv ; intuition.
  assert (Main := Temp' T T' y_cond).
  clear Temp Temp' T T'.
  assert (x1_lt_x2 : x1 < x2).
   apply Rlt_trans with (r2:=x) ; assumption.
   assert (f_cont_myinterv : forall a : R, x1 <= a <= x2 -> continuity_pt f a).
    intros ; apply f_cont_interv ; split. 
    apply Rle_trans with (r2 := x1) ; intuition.
    apply Rle_trans with (r2 := x2) ; intuition.
   elim (f_interv_is_interv f x1 x2 y x1_lt_x2 Main f_cont_myinterv) ; intros x' Temp.
   destruct Temp as (x'_encad,f_x'_y).
   rewrite <- f_x_b ; rewrite <- f_x'_y.
   unfold comp in f_eq_g. rewrite f_eq_g. rewrite f_eq_g.
   unfold id.
   assert (x'_encad2 : x - eps <= x' <= x + eps).
    split.
    apply Rle_trans with (r2:=x1) ; [ apply RmaxLess1|] ; intuition.
    apply Rle_trans with (r2:=x2) ; [ | apply Rmin_l] ; intuition.
    assert (x1_lt_x' : x1 < x').
     apply Sublemma3.
     assert (x1_neq_x' : x1 <> x').
      intro Hfalse. rewrite Hfalse, f_x'_y in y_cond.
      assert (Hf : Rabs (y - f x) < f x - y).
       apply Rlt_le_trans with (r2:=Rmin (f x - y) (f x2 - f x)).
{
assumption.
}
       apply Rmin_l.
      assert(Hfin : f x - y < f x - y).
       apply Rle_lt_trans with (r2:=Rabs (y - f x)).
       replace (Rabs (y - f x)) with (Rabs (f x - y)). apply RRle_abs.
       rewrite <- Rabs_Ropp. replace (- (f x - y)) with (y - f x). reflexivity.
{ rewrite Ropp_minus_distr. reflexivity. }
{
eapply Rlt_le_trans.
exact y_cond.
apply Rmin_l.
}
      apply (Rlt_irrefl (f x - y)) ; assumption.
      split ; intuition.
     assert (x'_lb : x - eps < x').
      apply Sublemma3.
      split. intuition. apply Rlt_not_eq.
      apply Rle_lt_trans with (r2:=x1) ; [ apply RmaxLess1|] ; intuition.
     assert (x'_lt_x2 : x' < x2).
     apply Sublemma3.
     assert (x1_neq_x' : x' <> x2).
      intro Hfalse. rewrite <- Hfalse, f_x'_y in y_cond.
      assert (Hf : Rabs (y - f x) < y - f x).
       apply Rlt_le_trans with (r2:=Rmin (f x - f x1) (y - f x)).
{
assumption.
}
       apply Rmin_r.
      assert(Hfin : y - f x < y - f x).
       apply Rle_lt_trans with (r2:=Rabs (y - f x)). apply RRle_abs.
{
eapply Rlt_le_trans.
exact y_cond.
apply Rmin_r.
}
      apply (Rlt_irrefl (y - f x)) ; assumption.
      split ; intuition.
     assert (x'_ub : x' < x + eps).
      apply Sublemma3.
      split. intuition. apply Rlt_not_eq.
      apply Rlt_le_trans with (r2:=x2) ; [ |rewrite Hx2 ; apply Rmin_l] ; intuition.
{
    apply Rabs_def1.
unfold Rminus.
apply Rplus_lt_reg_r with x.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
rewrite Rplus_comm.
assumption.

unfold Rminus.
apply Rplus_lt_reg_r with x.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
rewrite Rplus_comm.
assumption.
}
    assumption.
    split. apply Rle_trans with (r2:=x1) ; intuition.
    apply Rle_trans with (r2:=x2) ; intuition.
Qed.

Lemma continuity_pt_recip_interv : forall (f g:R->R) (lb ub : R) (Pr1:lb < ub),
       (forall x y, lb <= x -> x < y -> y <= ub -> f x < f y) ->
       (forall x, f lb <= x -> x <= f ub -> (comp f g) x = id x) ->
       (forall x, f lb <= x -> x <= f ub -> lb <= g x <= ub) ->
       (forall a, lb <= a <= ub -> continuity_pt f a) ->
       forall b,
       f lb < b < f ub ->
       continuity_pt g b.
Proof.
intros f g lb ub lb_lt_ub f_incr_interv f_eq_g g_wf.
assert (g_eq_f_prelim := leftinv_is_rightinv_interv f g lb ub f_incr_interv f_eq_g).
assert (g_eq_f : forall x, lb <= x <= ub -> (comp g f) x = id x).
intro x ; apply g_eq_f_prelim ; assumption.
apply (continuity_pt_recip_prelim f g lb ub lb_lt_ub f_incr_interv g_eq_f).
Qed.

(** *   Derivability of the reciprocal function        *)

Lemma derivable_pt_lim_recip_interv : forall (f g:R->R) (lb ub x:R)
       (Prf:forall a : R, g lb <= a <= g ub -> derivable_pt f a) (Prg : continuity_pt g x),
       lb < ub ->
       lb < x < ub ->
       forall (Prg_incr:g lb <= g x <= g ub),
       (forall x, lb <= x <= ub -> (comp f g) x = id x) ->
       derive_pt f (g x) (Prf (g x) Prg_incr) <> R0 ->
       derivable_pt_lim g x (R1 / derive_pt f (g x) (Prf (g x) Prg_incr)).
Proof.
  intros f g lb ub x Prf g_cont_pur lb_lt_ub x_encad Prg_incr f_eq_g df_neq.
  assert (x_encad2 : lb <= x <= ub).
{
  split ; apply Rlt_le ; intuition.
}
{
  elim (Prf (g x)); simpl; intros l Hl.
  unfold derivable_pt_lim.
  intros eps eps_pos.
  pose (y := g x).
  assert (Hlinv := limit_inv).
  assert (Hf_deriv : forall eps:R,
  R0 < eps ->
  exists delta : posreal,
  (forall h:R,
  h <> R0 -> Rabs h < delta -> Rabs ((f (g x + h) - f (g x)) / h - l) < eps)).
{
  intros eps0 eps0_pos.
  red in Hl ; red in Hl. elim (Hl eps0 eps0_pos).
  intros deltatemp Htemp.
  exists deltatemp ; exact Htemp.
}
{
  elim (Hf_deriv eps eps_pos).
  intros deltatemp Htemp.
  red in Hlinv ; red in Hlinv ; unfold dist in Hlinv ; unfold R_dist in Hlinv.
  assert (Hlinv' := Hlinv (fun h => (f (y+h) - f y)/h) (fun h => h <> R0) l R0).
  unfold limit1_in, limit_in, dist in Hlinv' ; simpl in Hlinv'. unfold R_dist in Hlinv'.
  assert (Premisse : (forall eps : R,
  R0 < eps ->
  exists alp : R,
  R0 < alp /\
  (forall x : R,
  (fun h => h <> R0) x /\ Rabs (x - R0) < alp ->
  Rabs ((f (y + x) - f y) / x - l) < eps))).
{
  intros eps0 eps0_pos.
  elim (Hf_deriv eps0 eps0_pos).
  intros deltatemp' Htemp'.
  exists deltatemp'.
  split.
{
  exact deltatemp'.(cond_pos).
}
{
  intros htemp cond.
  apply (Htemp' htemp).
{
  exact (proj1 cond).
}
{
  replace (htemp) with (htemp - R0).
{
  exact (proj2 cond).
}
{
  intuition.
}
}
}
}
{
  assert (Premisse2 : l <> R0).
{
  intro l_null.
  rewrite l_null in Hl.
  apply df_neq.
  rewrite derive_pt_eq.
  exact Hl.
}
{
  elim (Hlinv' Premisse Premisse2 eps eps_pos).
  intros alpha cond.
  assert (alpha_pos := proj1 cond) ; assert (inv_cont := proj2 cond) ; clear cond.
  unfold derivable, derivable_pt, derivable_pt_abs, derivable_pt_lim in Prf.
  elim (Hl eps eps_pos).
  intros delta f_deriv.
  assert (g_cont := g_cont_pur).
  unfold continuity_pt, continue_in, limit1_in, limit_in in g_cont.
  pose (mydelta := Rmin delta alpha).
  assert (mydelta_pos : R0 < mydelta).
{
  unfold mydelta, Rmin.
  case (Rle_dec delta alpha).
{
  intro ; exact (delta.(cond_pos)).
}
{
  intro ; exact alpha_pos.
}
}
{
  elim (g_cont mydelta mydelta_pos).
  intros delta' new_g_cont.
  assert(delta'_pos := proj1 (new_g_cont)).
  clear g_cont ; assert (g_cont := proj2 (new_g_cont)) ; clear new_g_cont.
  pose (mydelta'' := Rmin delta' (Rmin (x - lb) (ub - x))).
  assert(mydelta''_pos : R0 < mydelta'').
{
   unfold mydelta''.
   apply Rmin_pos ; [intuition | apply Rmin_pos] ; apply Rgt_minus ; intuition.
}
{
  pose (delta'' := mkposreal mydelta'' mydelta''_pos: posreal).
  exists delta''.
  intros h h_neq h_le_delta'.
  assert (lb <= x +h <= ub).
{
  assert (Sublemma2 : forall x y, Rabs x < Rabs y -> R0 < y -> x < y).
{
  intros m n Hyp_abs y_pos. apply Rlt_le_trans with (r2:=Rabs n).
{
  apply Rle_lt_trans with (r2:=Rabs m) ; [ | assumption] ; apply RRle_abs.
}
{
  apply Req_le ; apply Rabs_right ; apply Rgt_ge ; assumption.
}
}
{
  assert (lb <= x + h <= ub).
{
  split.
{
  assert (Sublemma : forall x y z, -z <= y - x -> x <= y + z).
{
  intros.
  apply Ropp_le_cancel.
  rewrite Ropp_plus_distr.
  apply Rplus_le_reg_l with y0.
  rewrite <- Rplus_assoc, Rplus_opp_r, Rplus_0_l.
  assumption.
}
{
   apply Sublemma.
   apply Rlt_le ; apply Sublemma2.
{
  rewrite Rabs_Ropp.
  apply Rlt_le_trans with (r2:=x-lb) ; [| apply RRle_abs] ;
  apply Rlt_le_trans with (r2:=Rmin (x - lb) (ub - x)) ; [| apply Rmin_l] ;
  apply Rlt_le_trans with (r2:=Rmin delta' (Rmin (x - lb) (ub - x))).
{
  apply Rlt_le_trans with (r2:=delta'').
  { assumption. }
  {
    right.
    reflexivity.
  }
}
{ apply Rmin_r. }
}
{
  apply Rgt_minus.
  apply x_encad.
}
}
}
{
  assert (Sublemma : forall x y z, y <= z - x -> x + y <= z).
{
  intros.
  apply Rplus_le_reg_l with (-x0).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
  rewrite Rplus_comm.
  assumption.
}
{
  apply Sublemma.
  apply Rlt_le.
  apply Sublemma2.
{
  apply Rlt_le_trans with (r2:=ub-x).
  2:apply RRle_abs.
  apply Rlt_le_trans with (r2:=Rmin (x - lb) (ub - x)).
  2:apply Rmin_r.
  apply Rlt_le_trans with (r2:=Rmin delta' (Rmin (x - lb) (ub - x))).
  2:apply Rmin_r.
  assumption.
}
{
  apply Rlt_le_trans with (r2:=delta'').
  { assumption. }
  {
    apply Rle_trans with (r2:=Rmin delta' (Rmin (x - lb) (ub - x))).
  {
    fold mydelta''.
    right.
    reflexivity.
  }
  {
    apply Rle_trans with (r2:=Rmin (x - lb) (ub - x)).
    { apply Rmin_r. }
    { apply Rmin_r. }
  }
}
}
}
}
}
{
  replace ((g (x + h) - g x) / h) with (R1/ (h / (g (x + h) - g x))).
{
  assert (Hrewr : h = (comp f g ) (x+h) - (comp f g) x).
{
  rewrite f_eq_g.
{
  rewrite f_eq_g.
  unfold id.
{
  rewrite Rplus_comm.
  unfold Rminus.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  reflexivity.
}
{ assumption. }
}
{ assumption. }
}
{
  split.
  2:apply H.
 assert (Sublemma : forall x y z, - z <= y - x -> x <= y + z).
{
  intros.
  apply Rplus_le_reg_r with (-z).
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
  apply Rplus_le_reg_l with (-x0).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
  rewrite Rplus_comm.
  assumption.
}
{
  apply Sublemma.
  apply Rlt_le.
  apply Sublemma2.
{
  rewrite Rabs_Ropp.
  apply Rlt_le_trans with (r2:=x-lb).
  2:apply RRle_abs.
  apply Rlt_le_trans with (r2:=Rmin (x - lb) (ub - x)).
  2:apply Rmin_l.
  apply Rlt_le_trans with (r2:=Rmin delta' (Rmin (x - lb) (ub - x))).
  2:apply Rmin_r.
  assumption.
}
{
  apply Rgt_minus.
  apply x_encad.
}
}
}
}
{
  assert(g (x + h) - g x <> R0).
  {
    intro Hfalse.
    assert (Hf : g (x+h) = g x).
    {
      eapply Rplus_eq_reg_r.
      symmetry.
      rewrite Rplus_opp_r.
      symmetry.
      assumption.
    }
    assert ((comp f g) (x+h) = (comp f g) x).
    {
      unfold comp.
      rewrite Hf.
      reflexivity.
    }
    {
      assert (Main : x+h = x).
      {
        replace (x +h) with (id (x+h)).
        2:{
          unfold id.
          reflexivity.
        }
        assert (Temp : x = id x).
        {
          unfold id.
          reflexivity.
        }
        rewrite Temp at 2.
        clear Temp.
        rewrite <- f_eq_g.
        {
          rewrite <- f_eq_g.
          { assumption. }
          { assumption. }
        }
        { assumption. }
      }
      {
        assert (h = R0).
        {
          apply Rplus_0_r_uniq with (r:=x).
          assumption.
        }
        {
          apply h_neq.
          assumption.
        }
      }
    }
  }
  unfold Rdiv.
  rewrite Rmult_1_l.
  rewrite Rinv_mult_distr.
  rewrite Rmult_comm.
  rewrite Rinv_involutive.
  reflexivity.
  { assumption. }
  { assumption. }
  {
    apply Rinv_neq_0_compat.
    assumption.
  }
}
}
}
}
{
  replace ((g (x + h) - g x) / h) with (R1 / (h / (g (x + h) - g x))).
  {
    assert (Hrewr : h = (comp f g ) (x+h) - (comp f g) x).
    {
      rewrite f_eq_g.
      {
        rewrite f_eq_g.
        {
          unfold id.
          rewrite Rplus_comm.
          unfold Rminus.
          rewrite Rplus_assoc.
          rewrite Rplus_opp_r.
          rewrite Rplus_0_r.
          reflexivity.
        }
        { assumption. }
      }
      { assumption. }
    }
    {
      rewrite Hrewr at 1.
      unfold comp.
      replace (g(x+h)) with (g x + (g (x+h) - g(x))).
      2:{
        rewrite Rplus_minus.
        reflexivity.
      }
      pose (h':=g (x+h) - g x).
      replace (g (x+h) - g x) with h'.
      2:{
        subst h'.
        reflexivity.
      }
      replace (g x + h' - g x) with h'.
      2:{
        rewrite Rplus_comm.
        unfold Rminus.
        rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
        reflexivity.
      }
      assert (h'_neq : h' <> R0).
      {
        unfold h'.
        intro Hfalse.
        unfold Rminus in Hfalse.
        apply Rminus_diag_uniq in Hfalse.
        assert (Hfalse' : (comp f g) (x+h) = (comp f g) x).
        {
          intros.
          unfold comp.
          rewrite Hfalse.
          reflexivity.
        }
        {
          rewrite f_eq_g in Hfalse'.
          rewrite f_eq_g in Hfalse'.
          {
            unfold id in Hfalse'.
            apply Rplus_0_r_uniq in Hfalse'.
            apply h_neq.
            exact Hfalse'.
          }
          { assumption. }
          { assumption. }
        }
      }
      {
        unfold Rdiv at 1 3.
        rewrite Rmult_1_l.
        rewrite Rmult_1_l.
        apply inv_cont.
        split.
        { exact h'_neq. }
        {
          rewrite Rminus_0_r. 
          unfold continuity_pt in g_cont_pur.
          unfold continue_in in g_cont_pur.
          unfold limit1_in in g_cont_pur.
          unfold limit_in in g_cont_pur.
          elim (g_cont_pur mydelta mydelta_pos).
          intros delta3 cond3.
          unfold dist in cond3.
          simpl in cond3.
          unfold R_dist in cond3.
          unfold h'.
          assert (mydelta_le_alpha : mydelta <= alpha).
          {
            unfold mydelta.
            unfold Rmin.
            case (Rle_dec delta alpha).
            {
              intro.
              assumption.
            }
            {
              intro.
              right.
              reflexivity.
            }
          }
          {
            apply Rlt_le_trans with (r2:=mydelta).
            {
              unfold dist in g_cont.
              simpl in g_cont.
              unfold R_dist in g_cont.
              apply g_cont.
              split.
              {
                unfold D_x.
                simpl.
                split.
                {
                  unfold no_cond.
                  exact I.
                }
                {
                  intro Hfalse.
                  apply h_neq.
                  apply (Rplus_0_r_uniq x).
                  symmetry.
                  assumption.
                }
              }
              {
                replace (x + h - x) with h.
                2:{
                  unfold Rminus.
                  rewrite Rplus_comm.
                  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
                  reflexivity.
                }
                apply Rlt_le_trans with (r2:=delta'').
                { assumption. }
                {
                  apply Rle_trans with (r2:=mydelta'').
                  {
                    apply Req_le.
                    unfold delta''.
                    simpl.
                    reflexivity.
                  }
                  { apply Rmin_l. }
                }
              }
            }
            { assumption. }
          }
        }
      }
    }
  }
  {
    assert(g (x + h) - g x <> R0).
    {
      intro Hfalse.
      apply h_neq.
      apply (Rplus_0_r_uniq x).
      assert (Hfin : (comp f g) (x+h) = (comp f g) x).
      {
        apply Rminus_diag_uniq in Hfalse.
        unfold comp.
        rewrite Hfalse.
        reflexivity.
      }
      {
        rewrite f_eq_g in Hfin.
        {
          rewrite f_eq_g in Hfin.
          {
            unfold id in Hfin.
            exact Hfin.
          }
          { assumption. }
        }
        { assumption. }
      }
    }
    unfold Rdiv.
    rewrite Rmult_1_l.
    rewrite Rinv_mult_distr.
    rewrite Rmult_comm.
    apply Rmult_eq_compat_r.
    rewrite Rinv_involutive.
    reflexivity.
    { assumption. }
    { assumption. }
    {
      apply Rinv_neq_0_compat.
      assumption.
    }
  }
}
}
}
}
}
}
}
Qed.

Lemma derivable_pt_recip_interv_prelim0 : forall (f g : R -> R) (lb ub x : R)
       (Prf : forall a : R, g lb <= a <= g ub -> derivable_pt f a),
       continuity_pt g x ->
       lb < ub ->
       lb < x < ub ->
       forall Prg_incr : g lb <= g x <= g ub,
       (forall x0 : R, lb <= x0 <= ub -> comp f g x0 = id x0) ->
       derive_pt f (g x) (Prf (g x) Prg_incr) <> R0 ->
       derivable_pt g x.
Proof.
intros f g lb ub x Prf g_cont_pt lb_lt_ub x_encad Prg_incr f_eq_g Df_neq.
unfold derivable_pt, derivable_pt_abs.
exists (R1 / derive_pt f (g x) (Prf (g x) Prg_incr)).
apply derivable_pt_lim_recip_interv ; assumption.
Qed.

Lemma derivable_pt_recip_interv_prelim1 :forall (f g:R->R) (lb ub x : R),
         lb < ub ->
         f lb < x < f ub ->
         (forall x : R, f lb <= x -> x <= f ub -> comp f g x = id x) ->
         (forall x : R, f lb <= x -> x <= f ub -> lb <= g x <= ub) ->
         (forall x y : R, lb <= x -> x < y -> y <= ub -> f x < f y) ->
         (forall a : R, lb <= a <= ub -> derivable_pt f a) ->
         derivable_pt f (g x).
Proof.
intros f g lb ub x lb_lt_ub x_encad f_eq_g g_ok f_incr f_derivable.
 apply f_derivable.
 assert (Left_inv := leftinv_is_rightinv_interv f g lb ub f_incr f_eq_g g_ok).
 replace lb with ((comp g f) lb).
 replace ub with ((comp g f) ub).
 unfold comp.
 assert (Temp:= f_incr_implies_g_incr_interv f g lb ub lb_lt_ub f_incr f_eq_g g_ok).
 split ; apply Rlt_le ; apply Temp ; intuition.
 apply Left_inv ; intuition.
 apply Left_inv ; intuition.
Qed.

Lemma derivable_pt_recip_interv : forall (f g:R->R) (lb ub x : R)
         (lb_lt_ub:lb < ub) (x_encad:f lb < x < f ub)
         (f_eq_g:forall x : R, f lb <= x -> x <= f ub -> comp f g x = id x)
         (g_wf:forall x : R, f lb <= x -> x <= f ub -> lb <= g x <= ub)
         (f_incr:forall x y : R, lb <= x -> x < y -> y <= ub -> f x < f y)
         (f_derivable:forall a : R, lb <= a <= ub -> derivable_pt f a),
         derive_pt f (g x)
              (derivable_pt_recip_interv_prelim1 f g lb ub x lb_lt_ub
              x_encad f_eq_g g_wf f_incr f_derivable)
         <> R0 ->
         derivable_pt g x.
Proof.
intros f g lb ub x lb_lt_ub x_encad f_eq_g g_wf f_incr f_derivable Df_neq.
 assert(g_incr : g (f lb) < g x < g (f ub)).
  assert (Temp:= f_incr_implies_g_incr_interv f g lb ub lb_lt_ub f_incr f_eq_g g_wf).
  split ; apply Temp ; intuition.
  exact (proj1 x_encad). apply Rlt_le ; exact (proj2 x_encad).
  apply Rlt_le ; exact (proj1 x_encad). exact (proj2 x_encad).
 assert(g_incr2 :  g (f lb) <= g x <= g (f ub)).
  split ; apply Rlt_le ; intuition.
 assert (g_eq_f :=  leftinv_is_rightinv_interv f g lb ub f_incr f_eq_g g_wf).
 unfold comp, id in g_eq_f.
 assert (f_derivable2 : forall a : R, g (f lb) <= a <= g (f ub) -> derivable_pt f a).
  intros a a_encad ; apply f_derivable.
   rewrite g_eq_f in a_encad ; rewrite g_eq_f in a_encad ; intuition.
 apply derivable_pt_recip_interv_prelim0 with (f:=f) (lb:=f lb) (ub:=f ub)
     (Prf:=f_derivable2) (Prg_incr:=g_incr2).
 apply continuity_pt_recip_interv with (f:=f) (lb:=lb) (ub:=ub) ; intuition.
 apply derivable_continuous_pt ; apply f_derivable ; intuition.
 exact (proj1 x_encad). exact (proj2 x_encad).  apply f_incr ; intuition.
 assumption.
 intros x0 x0_encad ; apply f_eq_g ; intuition.
 rewrite pr_nu_var2_interv with (g:=f) (lb:=lb) (ub:=ub) (pr2:=derivable_pt_recip_interv_prelim1 f g lb ub x lb_lt_ub x_encad
      f_eq_g g_wf f_incr f_derivable) ; [| |rewrite g_eq_f in g_incr ; rewrite g_eq_f in g_incr| ] ; intuition.
Qed.

(****************************************************)
(** *   Value of the derivative of the reciprocal function        *)
(****************************************************)

Lemma derive_pt_recip_interv_prelim0 : forall (f g:R->R) (lb ub x:R)
       (Prf:derivable_pt f (g x)) (Prg:derivable_pt g x),
       lb < ub ->
       lb < x < ub ->
       (forall x, lb < x < ub -> (comp f g) x = id x) ->
       derive_pt f (g x) Prf <> R0 ->
       derive_pt g x Prg = R1 / (derive_pt f (g x) Prf).
Proof.
  intros f g lb ub x Prf Prg lb_lt_ub x_encad local_recip Df_neq.
  replace (derive_pt g x Prg) with
  ((derive_pt g x Prg) * (derive_pt f (g x) Prf) * / (derive_pt f (g x) Prf)).
  unfold Rdiv.
  rewrite (Rmult_comm _ (/ derive_pt f (g x) Prf)).
  rewrite (Rmult_comm _ (/ derive_pt f (g x) Prf)). 
  apply Rmult_eq_compat_l. 
  rewrite Rmult_comm.
  rewrite <- derive_pt_comp.
  assert (x_encad2 : lb <= x <= ub) by intuition.
  {
    rewrite pr_nu_var2_interv with (g:=id) (pr2:= derivable_pt_id_interv lb ub x x_encad2) (lb:=lb) (ub:=ub).
    { admit. }
    assumption.
    assumption.
    assumption.
  }
 rewrite Rmult_assoc, Rinv_r.
 intuition.
 assumption.
Admitted.

Lemma derive_pt_recip_interv_prelim1_0 : forall (f g:R->R) (lb ub x:R), 
       lb < ub ->
       f lb < x < f ub ->
       (forall x y : R, lb <= x -> x < y -> y <= ub -> f x < f y) ->
       (forall x : R, f lb <= x -> x <= f ub -> lb <= g x <= ub) ->
       (forall x, f lb <= x -> x <= f ub -> (comp f g) x = id x) ->
       lb < g x < ub.
Proof.
intros f g lb ub x lb_lt_ub x_encad f_incr g_wf f_eq_g.
 assert (Temp:= f_incr_implies_g_incr_interv f g lb ub lb_lt_ub f_incr f_eq_g g_wf).
 assert (Left_inv := leftinv_is_rightinv_interv f g lb ub f_incr f_eq_g g_wf).
 unfold comp, id in Left_inv.
 split ; [rewrite <- Left_inv with (x:=lb) | rewrite <- Left_inv ].
 apply Temp ; intuition.
 intuition.
 apply Temp ; intuition.
 intuition.
Qed.

Lemma derive_pt_recip_interv_prelim1_1 : forall (f g:R->R) (lb ub x:R), 
       lb < ub ->
       f lb < x < f ub ->
       (forall x y : R, lb <= x -> x < y -> y <= ub -> f x < f y) ->
       (forall x : R, f lb <= x -> x <= f ub -> lb <= g x <= ub) ->
       (forall x, f lb <= x -> x <= f ub -> (comp f g) x = id x) ->
       lb <= g x <= ub.
Proof.
intros f g lb ub x lb_lt_ub x_encad f_incr g_wf f_eq_g.
 assert (Temp := derive_pt_recip_interv_prelim1_0 f g lb ub x lb_lt_ub x_encad f_incr g_wf f_eq_g).
 split ; apply Rlt_le ; intuition.
Qed.

Lemma derive_pt_recip_interv : forall (f g:R->R) (lb ub x:R)
       (lb_lt_ub:lb < ub) (x_encad:f lb < x < f ub)
       (f_incr:forall x y : R, lb <= x -> x < y -> y <= ub -> f x < f y)
       (g_wf:forall x : R, f lb <= x -> x <= f ub -> lb <= g x <= ub)
       (Prf:forall a : R, lb <= a <= ub -> derivable_pt f a)
       (f_eq_g:forall x, f lb <= x -> x <= f ub -> (comp f g) x = id x)
       (Df_neq:derive_pt f (g x) (derivable_pt_recip_interv_prelim1 f g lb ub x
                 lb_lt_ub x_encad f_eq_g g_wf f_incr Prf) <> R0),
       derive_pt g x (derivable_pt_recip_interv f g lb ub x lb_lt_ub x_encad f_eq_g
                 g_wf f_incr Prf Df_neq)
       =
       R1 / (derive_pt f (g x) (Prf (g x) (derive_pt_recip_interv_prelim1_1 f g lb ub x
       lb_lt_ub x_encad f_incr g_wf f_eq_g))).
Proof.
intros.
 assert(g_incr := (derive_pt_recip_interv_prelim1_1 f g lb ub x lb_lt_ub
        x_encad f_incr g_wf f_eq_g)).
 apply derive_pt_recip_interv_prelim0 with (lb:=f lb) (ub:=f ub) ;
 [intuition |assumption | intuition |].
 intro Hfalse ; apply Df_neq.  rewrite pr_nu_var2_interv with (g:=f) (lb:=lb) (ub:=ub)
        (pr2:= (Prf (g x) (derive_pt_recip_interv_prelim1_1 f g lb ub x lb_lt_ub x_encad
                 f_incr g_wf f_eq_g))) ;
 [intuition | intuition | | intuition].
 exact (derive_pt_recip_interv_prelim1_0 f g lb ub x lb_lt_ub x_encad f_incr g_wf f_eq_g).
Qed.
  
(****************************************************)
(** * Existence of the derivative of a function which is the limit of a sequence of functions *)
(****************************************************)

(* begin hide *)
Lemma ub_lt_2_pos : forall x ub lb, lb < x -> x < ub -> R0 < (ub-lb)/R2.
Proof.
intros x ub lb lb_lt_x x_lt_ub.
unfold Rdiv, Rminus.
rewrite Rmult_plus_distr_r.
eapply Rplus_lt_reg_r.
rewrite Rplus_assoc.
rewrite <- Ropp_mult_distr_l.
rewrite Rplus_opp_l, Rplus_0_r.
rewrite Rplus_0_l.
apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat. exact Rlt_0_2.
apply Rlt_trans with x;assumption.
Qed.

Definition mkposreal_lb_ub (x lb ub:R) (lb_lt_x:lb<x) (x_lt_ub:x<ub) : posreal.
 apply (mkposreal ((ub-lb)/R2) (ub_lt_2_pos x ub lb lb_lt_x x_lt_ub)).
Defined.
(* end hide *)

Lemma derivable_pt_lim_CVU : forall (fn fn':nat -> R -> R) (f g:R->R)
      (x:R) c r, Boule c r x ->
      (forall y n, Boule c r y -> derivable_pt_lim (fn n) y (fn' n y)) ->
      (forall y, Boule c r y -> Un_cv (fun n => fn n y) (f y)) ->
      (CVU fn' g c r) ->
      (forall y, Boule c r y -> continuity_pt g y) ->
      derivable_pt_lim f x (g x).
Proof.
  intros fn fn' f g x c' r xinb Dfn_eq_fn' fn_CV_f fn'_CVU_g g_cont eps eps_pos.
  assert (eps_8_pos : R0 < eps / R8).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { assumption. }
    {
      apply Rinv_0_lt_compat.
      exact Rlt_0_8.
    }
  }
  elim (g_cont x xinb _ eps_8_pos).
  clear g_cont.
  intros delta1 (delta1_pos, g_cont).
  destruct (Ball_in_inter _ _ _ _ _ xinb (Boule_center x (mkposreal _ delta1_pos))) as [delta Pdelta].
  exists delta.
  intros h hpos hinbdelta.
  assert (eps'_pos : R0 < (Rabs h) * eps / R4).
  {
    unfold Rdiv.
    rewrite Rmult_assoc.
    apply Rmult_lt_0_compat.
    {
      apply Rabs_pos_lt.
      assumption.
    }
    {
      apply Rmult_lt_0_compat.
      { assumption. }
      {
        apply Rinv_0_lt_compat.
        exact Rlt_0_4.
      }
    }
  }
  {
    destruct (fn_CV_f x xinb ((Rabs h) * eps / R4) eps'_pos) as [N2 fnx_CV_fx].
    assert (xhinbxdelta : Boule x delta (x + h)).
    {
      clear -hinbdelta.
      apply Rabs_def2 in hinbdelta.
      unfold Boule.
      destruct hinbdelta.
      apply Rabs_def1.
      {
        unfold Rminus.
        rewrite Rplus_comm.
        rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
        assumption.
      }
      {
        unfold Rminus.
        rewrite Rplus_comm.
        rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
        assumption.
      }
    }
    {
      assert (t : Boule c' r (x + h)).
      {
        apply Pdelta in xhinbxdelta.
        apply xhinbxdelta.
      }
      {
        destruct (fn_CV_f (x+h) t ((Rabs h) * eps / R4) eps'_pos) as [N1 fnxh_CV_fxh].
        clear fn_CV_f t.
        destruct (fn'_CVU_g (eps/R8) eps_8_pos) as [N3 fn'c_CVU_gc].
        pose (N := ((N1 + N2) + N3)%nat).
        assert (Main : Rabs ((f (x+h) - fn N (x+h)) - (f x - fn N x) + (fn N (x+h) - fn N x - h * (g x))) < (Rabs h)*eps).
        {
          apply Rle_lt_trans with (Rabs (f (x + h) - fn N (x + h) - (f x - fn N x)) +  Rabs ((fn N (x + h) - fn N x - h * g x))).
          { apply Rabs_triang. }
          {
            apply Rle_lt_trans with (Rabs (f (x + h) - fn N (x + h)) + Rabs (- (f x - fn N x)) + Rabs (fn N (x + h) - fn N x - h * g x)).
            {
              apply Rplus_le_compat_r.
              apply Rabs_triang.
            }
            {
            rewrite Rabs_Ropp.
            case (Rlt_le_dec h R0).
            {
              intro sgn_h.
              assert (pr1 : forall c : R, x + h < c < x -> derivable_pt (fn N) c).
              {
                intros c c_encad.
                unfold derivable_pt.
                exists (fn' N c).
                apply Dfn_eq_fn'.
                assert (t : Boule x delta c).
                {
                  apply Rabs_def2 in xhinbxdelta.
                  destruct xhinbxdelta.
                  destruct c_encad.
                  apply Rabs_def2 in xinb.
                  apply Rabs_def1.
                  {
                    unfold Rminus.
                    apply Rplus_lt_reg_r with x.
                    rewrite Rplus_assoc, Rplus_opp_l, Rplus_comm.
                    apply Rplus_lt_compat.
                    { apply cond_pos. }
                    { assumption. }
                  }
                  {
                    unfold Rminus in H0.
                    rewrite Rplus_comm in H0.
                    rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l in H0.
                    unfold Rminus.
                    apply Rplus_lt_reg_l with h.
                    rewrite Rplus_comm.
                    apply Rplus_lt_compat.
                    { assumption. }
                    {
                      apply Rplus_lt_reg_r with x.
                      rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
                      assumption.
                    }
                  }
                }
                {
                  apply Pdelta in t.
                  apply t.
                }
              }
              {
                assert (pr2 : forall c : R, x + h < c < x -> derivable_pt id c).
                {
                  intros.
                  apply derivable_id.
                }
                {
                  assert (xh_x : x+h < x).
                  {
                    pattern x at 2;rewrite <- Rplus_0_r.
                    apply Rplus_lt_compat_l.
                    assumption.
                  }
                  assert (pr3 : forall c : R, x + h <= c <= x -> continuity_pt (fn N) c).
                  {
                    intros c c_encad.
                    apply derivable_continuous_pt.
                    exists (fn' N c).
                    apply Dfn_eq_fn'.
                    destruct c_encad.
                    assert (t : Boule x delta c).
                    {
                      apply Rabs_def2 in xhinbxdelta.
                      destruct xhinbxdelta.
                      apply Rabs_def2 in xinb.
                      apply Rabs_def1.
                      {
                        apply Rplus_lt_reg_r with x.
                        unfold Rminus.
                        rewrite Rplus_assoc, Rplus_opp_l, Rplus_comm.
                        apply Rplus_lt_le_compat.
                        { apply cond_pos. }
                        { assumption. }
                      }
                      {
                        rewrite Rplus_comm in H2.
                        unfold Rminus in H2.
                        rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r in H2.
                        apply Rplus_lt_reg_r with h.
                        unfold Rminus.
                        rewrite Rplus_comm.
                        apply Rplus_le_lt_compat.
                        {
                          apply Rplus_le_reg_r with x.
                          rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
                          assumption.
                        }
                        { assumption. }
                      }
                    }
                    {
                      apply Pdelta in t.
                      apply t.
                    }
                  }
                  {
                    assert (pr4 : forall c : R, x + h <= c <= x -> continuity_pt id c).
                    {
                      intros.
                      apply derivable_continuous.
                      apply derivable_id.
                    }
                    {
                      destruct (MVT (fn N) id (x+h) x pr1 pr2 xh_x pr3 pr4) as [c [P Hc]].
                      assert (Hc' : h * derive_pt (fn N) c (pr1 c P) = (fn N (x+h) - fn N x)).
                      {
                         apply Rmult_eq_reg_l with (-R1).
                          {
                            replace (-R1 * (h * derive_pt (fn N) c (pr1 c P))) with (-h * derive_pt (fn N) c (pr1 c P)).
                            2:{
                              change (-R1) with (-R1).
                              repeat rewrite <- Ropp_mult_distr_l.
                              rewrite Rmult_1_l.
                              reflexivity.
                            }
                            replace (-R1 * (fn N (x + h) - fn N x)) with (- (fn N (x + h) - fn N x)).
                            2:{
                              change (-R1) with (-R1).
                              repeat rewrite <- Ropp_mult_distr_l.
                              rewrite Rmult_1_l.
                              reflexivity.
                            }
                            replace (-h) with (id x - id (x + h)).
                            2:{
                              unfold id.
                              unfold Rminus.
                              rewrite Ropp_plus_distr.
                              rewrite <- Rplus_assoc, Rplus_opp_r, Rplus_0_l.
                              reflexivity.
                            }
                            rewrite <- Rmult_1_r.
                            replace R1 with (derive_pt id c (pr2 c P)).
                            2:{
                              clear.
                              unfold derive_pt.
                              unfold derivable_pt in pr2.
                              unfold derivable_pt_abs in pr2.
                              destruct (pr2 c P) as [ l hl ].
                              simpl.
                              eapply uniqueness_limite.
                              apply hl.
                              apply derivable_pt_lim_id.
                            }
                            replace (- (fn N (x + h) - fn N x)) with (fn N x - fn N (x + h)).
                            2:{
                              unfold Rminus.
                              rewrite Ropp_plus_distr, Ropp_involutive, Rplus_comm.
                              reflexivity.
                            }
                            assumption.
                          }
                          {
                            apply Rlt_not_eq.
                            apply Ropp_lt_cancel.
                            change (-R1) with (-R1).
                            rewrite Ropp_involutive, Ropp_0.
                            exact Rlt_0_1.
                          }
                        }
                        {
                          rewrite <- Hc'.
                          clear Hc Hc'.
                          replace (derive_pt (fn N) c (pr1 c P)) with (fn' N c).
                          {
                            replace (h * fn' N c - h * g x) with (h * (fn' N c - g x)).
                            2:{
                              unfold Rminus.
                              rewrite Ropp_mult_distr_r.
                              rewrite <- Rmult_plus_distr_l.
                              reflexivity.
                            }
                            rewrite Rabs_mult.
                            apply Rlt_trans with (Rabs h * eps / R4 + Rabs (f x - fn N x) + Rabs h * Rabs (fn' N c - g x)).
                            {
                              apply Rplus_lt_compat_r.
                              apply Rplus_lt_compat_r.
                              unfold R_dist in fnxh_CV_fxh.
                              rewrite Rabs_minus_sym.
                              apply fnxh_CV_fxh.
                              unfold N.
                              unfold ge.
                              rewrite <- plus_assoc.
                              apply le_plus_l.
                            }
                            {
                              apply Rlt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * Rabs (fn' N c - g x)).
                              {
                                apply Rplus_lt_compat_r.
                                apply Rplus_lt_compat_l.
                                unfold R_dist in fnx_CV_fx.
                                rewrite Rabs_minus_sym.
                                apply fnx_CV_fx.
                                unfold N.
                                unfold ge.
                                rewrite plus_comm.
                                rewrite plus_assoc.
                                apply le_plus_r.
                              }
                              {
                                replace (fn' N c - g x)  with ((fn' N c - g c) +  (g c - g x)).
                                2:{
                                  unfold Rminus.
                                  repeat rewrite <- Rplus_assoc.
                                  apply Rplus_eq_compat_r.
                                  repeat rewrite Rplus_assoc.
                                  rewrite Rplus_opp_l, Rplus_0_r.
                                  reflexivity.
                                }
                                apply Rle_lt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * Rabs (fn' N c - g c) + Rabs h * Rabs (g c - g x)).
                                {
                                  rewrite Rplus_assoc.
                                  rewrite Rplus_assoc.
                                  rewrite Rplus_assoc.
                                  apply Rplus_le_compat_l.
                                  apply Rplus_le_compat_l.
                                  rewrite <- Rmult_plus_distr_l.
                                  apply Rmult_le_compat_l.
                                  { apply Rabs_pos. }
                                  { apply Rabs_triang. }
                                }
                                {
                                  apply Rlt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * (eps / R8) + Rabs h * Rabs (g c - g x)).
                                  {
                                    apply Rplus_lt_compat_r.
                                    apply Rplus_lt_compat_l.
                                    apply Rmult_lt_compat_l.
                                    {
                                      apply Rabs_pos_lt.
                                      assumption.
                                    }
                                    {
                                      rewrite Rabs_minus_sym.
                                      apply fn'c_CVU_gc.
                                      {
                                        unfold N.
                                        rewrite plus_comm.
                                        apply Nat.le_add_r.
                                      }
                                      {
                                        assert (t : Boule x delta c).
                                        {
                                          destruct P.
                                          apply Rabs_def2 in xhinbxdelta.
                                          destruct xhinbxdelta.
                                          apply Rabs_def2 in xinb.
                                          apply Rabs_def1.
                                          {
                                            unfold Rminus.
                                            apply Rplus_lt_reg_r with x.
                                            rewrite Rplus_assoc, Rplus_opp_l, Rplus_comm.
                                            apply Rplus_lt_compat.
                                            { apply cond_pos. }
                                            { assumption. }
                                          }
                                          {
                                            unfold Rminus.
                                            unfold Rminus in H2.
                                            rewrite Rplus_comm in H2.
                                            rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l in H2.
                                            apply Rplus_lt_reg_r with h.
                                            rewrite Rplus_comm.
                                            apply Rplus_lt_compat.
                                            {
                                              apply Rplus_lt_reg_r with x.
                                              rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
                                              assumption.
                                            }
                                            { assumption. }
                                          }
                                        }
                                        {
                                          apply Pdelta in t.
                                          apply t.
                                        }
                                      }
                                    }
                                  }
                                  {
                                    apply Rlt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * (eps / R8) + Rabs h * (eps / R8)).
                                    {
                                      rewrite Rplus_assoc.
                                      rewrite Rplus_assoc.
                                      rewrite Rplus_assoc.
                                      rewrite Rplus_assoc.
                                      apply Rplus_lt_compat_l.
                                      apply Rplus_lt_compat_l.
                                      rewrite <- Rmult_plus_distr_l.
                                      rewrite <- Rmult_plus_distr_l.
                                      apply Rmult_lt_compat_l.
                                      {
                                        apply Rabs_pos_lt.
                                        assumption.
                                      }
                                      {
                                        apply Rplus_lt_compat_l.
                                        simpl in g_cont.
                                        apply g_cont.
                                        split.
                                        {
                                          unfold D_x.
                                          split.
                                          {
                                            unfold no_cond.
                                            exact I.
                                          }
                                          {
                                            apply Rgt_not_eq.
                                            exact (proj2 P).
                                          }
                                        }
                                        {
                                          apply Rlt_trans with (Rabs h).
                                          {
                                            apply Rabs_def1.
                                            {
                                              apply Rlt_trans with R0.
                                              {
                                                destruct P.
                                                unfold Rminus.
                                                apply Rplus_lt_reg_r with x.
                                                rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
                                                assumption.
                                              }
                                              {
                                                apply Rabs_pos_lt.
                                                assumption.
                                              }
                                            }
                                            {
                                              rewrite <- Rabs_Ropp, Rabs_pos_eq, Ropp_involutive.
                                              2:{
                                                apply Ropp_le_cancel.
                                                rewrite Ropp_0, Ropp_involutive.
                                                left.
                                                assumption.
                                              }
                                              destruct P.
                                              {
                                                unfold Rminus.
                                                apply Rplus_lt_reg_r with x.
                                                rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
                                                assumption.
                                              }
                                            }
                                          }
                                          {
                                            clear -Pdelta xhinbxdelta.
                                            apply Pdelta in xhinbxdelta.
                                            destruct xhinbxdelta as [_ P'].
                                            apply Rabs_def2 in P'.
                                            simpl in P'.
                                            destruct P'.
                                            apply Rabs_def1.
                                            {
                                              rewrite Rplus_comm in H.
                                              unfold Rminus in H.
                                              rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r in H.
                                              assumption.
                                            }
                                            {
                                              rewrite Rplus_comm in H0.
                                              unfold Rminus in H0.
                                              rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r in H0.
                                              assumption.
                                            }
                                          }
                                        }
                                      }
                                    }
                                    {
                                      rewrite Rplus_assoc.
                                      rewrite Rplus_assoc.
                                      rewrite <- Rmult_plus_distr_l.
                                      replace (
                                        Rabs h * eps / R4 + (Rabs h * eps / R4 + Rabs h * (eps / R8 + eps / R8))
                                      ) with (
                                        Rabs h * (eps / R4 + eps / R4 + eps / R8 + eps / R8)
                                      ).
                                      2:{
                                        unfold Rdiv.
                                        repeat rewrite Rmult_assoc.
                                        repeat rewrite <- Rmult_plus_distr_l.
                                        repeat rewrite <- Rplus_assoc.
                                        reflexivity.
                                      }
                                      apply Rmult_lt_compat_l.
                                      {
                                        apply Rabs_pos_lt.
                                        assumption.
                                      }
                                      {
                                        unfold Rdiv.
                                        repeat rewrite Rplus_assoc.
                                        repeat rewrite <- Rmult_plus_distr_l.
                                        pattern eps at 2;rewrite <- Rmult_1_r.
                                        apply Rmult_lt_compat_l.
                                        { assumption. }
                                        {
                                          apply Rmult_lt_reg_r with R8.
                                          { exact Rlt_0_8. }
                                          {
                                            repeat rewrite Rmult_plus_distr_r.
                                            rewrite Rinv_l.
                                            2:{ apply Rlt_not_eq'. exact Rlt_0_8. }
                                            replace R8 with (R4*R2).
                                            2:{
rewrite Rmult_comm, double.
unfold R8.
reflexivity.
                                            }
                                            repeat rewrite <- Rmult_assoc.
                                            rewrite Rinv_l.
                                            2:{ apply Rlt_not_eq'. exact Rlt_0_4. }
                                            repeat rewrite Rmult_1_l.
unfold R4. unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat_r.
pattern R1 at 1;rewrite <- Rplus_0_l.
pattern R1 at 1;rewrite <- Rplus_0_l.
repeat rewrite <- Rplus_assoc.
apply Rplus_lt_le_compat.
apply Rplus_lt_compat;exact Rlt_0_1.
right;reflexivity.
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                          {
                            assert (H := pr1 c P).
                            elim H.
                            clear H.
                            intros l Hl.
                            assert (Temp : l = fn' N c).
                            {
                               assert (bc'rc : Boule c' r c).
                              {
                                assert (t : Boule x delta c).
                                {
                                  clear - xhinbxdelta P.
                                  destruct P.
                                  apply Rabs_def2 in xhinbxdelta.
                                  destruct xhinbxdelta.
                                  apply Rabs_def1.
                                  {
                                    unfold Rminus.
                                    apply Rplus_lt_reg_r with x.
                                    rewrite Rplus_assoc, Rplus_opp_l, Rplus_comm.
                                    apply Rplus_lt_compat.
                                    { apply cond_pos. }
                                    { assumption. }
                                  }
                                  {
                                    unfold Rminus.
                                    apply Rplus_lt_reg_r with (x+h).
                                    repeat rewrite Rplus_assoc.
                                    rewrite (Rplus_comm c).
                                    apply Rplus_lt_compat.
                                    {
                                      rewrite Rplus_comm.
                                      assumption.
                                    }
                                    { assumption. }
                                  }
                                }
                                {
                                  apply Pdelta in t.
                                  apply t.
                                }
                              }
                              {
                                assert (Hl' := Dfn_eq_fn' c N bc'rc).
                                unfold derivable_pt_abs in Hl.
                                clear -Hl Hl'.
                                apply uniqueness_limite with (f:= fn N) (x:=c).
                                { assumption. }
                                { assumption. }
                              }
                            }
                            {
                              rewrite <- Temp.
                              assert (Hl' : derivable_pt (fn N) c).
                              {
                                exists l.
                                apply Hl.
                              }
                              {
                                rewrite pr_nu_var with (g:= fn N) (pr2:=Hl').
                                {
                                  elim Hl'.
                                  clear Hl'.
                                  intros l' Hl'.
                                  assert (Main : l = l').
                                  {
                                    apply uniqueness_limite with (f:= fn N) (x:=c).
                                    { assumption. }
                                    { assumption. }
                                  }
                                  {
                                    rewrite Main.
                                    reflexivity.
                                  }
                                }
                                { reflexivity. }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
              {
                intro sgn_h.
                assert (h_pos : R0 < h).
                {
                  case sgn_h.
                  {
                    intro Hyp.
                    assumption.
                  }
                  {
                    intro Hyp.
                    apply False_ind.
                    apply hpos.
                    symmetry.
                    assumption.
                  }
                }
                {
                  clear sgn_h.
                  assert (pr1 : forall c : R, x < c < x + h -> derivable_pt (fn N) c).
                  {
                    intros c c_encad.
                    unfold derivable_pt.
                    exists (fn' N c).
                    apply Dfn_eq_fn'.
                    assert (t : Boule x delta c).
                    {
                      apply Rabs_def2 in xhinbxdelta.
                      destruct xhinbxdelta.
                      destruct c_encad.
                      apply Rabs_def2 in xinb.
                      apply Rabs_def1.
                      {
                        unfold Rminus.
                        apply Rplus_lt_reg_r with (x+h).
                        rewrite Rplus_assoc.
                        rewrite (Rplus_comm (-x)).
                        rewrite Rplus_assoc.
                        rewrite (Rplus_comm x).
                        rewrite Rplus_assoc.
                        rewrite Rplus_opp_l, Rplus_0_r.
                        rewrite (Rplus_comm delta).
                        apply Rplus_lt_compat.
                        { assumption. }
                        {
                          pattern h;rewrite <- Rplus_0_r.
                          rewrite <- (Rplus_opp_l x).
                          rewrite <- Rplus_assoc.
                          rewrite Rplus_comm.
                          rewrite <- Rplus_assoc.
                          assumption.
                         }
                      }
                      {
                        apply Ropp_lt_cancel.
                        rewrite Ropp_minus_distr, Ropp_involutive.
                        apply Rplus_lt_reg_r with c.
                        unfold Rminus.
                        rewrite Rplus_assoc, Rplus_opp_l, Rplus_comm.
                        apply Rplus_lt_compat.
                        { apply cond_pos. }
                        { assumption. }
                      }
                    }
                    {
                      apply Pdelta in t.
                      apply t.
                    }
                  }
                  {
                    assert (pr2 : forall c : R, x < c < x + h -> derivable_pt id c).
                    {
                      intros.
                      apply derivable_id.
                    }
                    {
                      assert (xh_x : x < x + h).
                      {
                        pattern x at 1;rewrite <- Rplus_0_r.
                        apply Rplus_lt_compat_l.
                        assumption.
                      }
                      assert (pr3 : forall c : R, x <= c <= x + h -> continuity_pt (fn N) c).
                      {
                        intros c c_encad.
                        apply derivable_continuous_pt.
                        exists (fn' N c).
                        apply Dfn_eq_fn'.
                        destruct c_encad.
                        assert (t : Boule x delta c).
                        {
                          apply Rabs_def2 in xhinbxdelta.
                          destruct xhinbxdelta.
                          apply Rabs_def2 in xinb.
                          apply Rabs_def1.
                          {
                            unfold Rminus.
                            apply Rplus_lt_reg_r with (x+h).
                            rewrite Rplus_assoc.
                            rewrite (Rplus_comm (-x)).
                            rewrite Rplus_assoc.
                            rewrite (Rplus_comm x).
                            rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                            rewrite (Rplus_comm delta).
                            apply Rplus_le_lt_compat.
                            { assumption. }
                            {
                              pattern h;rewrite <- Rplus_0_r.
                              rewrite <- (Rplus_opp_l x).
                              rewrite <- Rplus_assoc.
                              rewrite Rplus_comm.
                              rewrite <- Rplus_assoc.
                              assumption.
                            }
                          }
                          {
                            apply Ropp_lt_cancel.
                            rewrite Ropp_minus_distr, Ropp_involutive.
                            unfold Rminus.
                            apply Rplus_lt_reg_r with c.
                            rewrite Rplus_assoc, Rplus_opp_l.
                            rewrite Rplus_comm.
                            apply Rplus_lt_le_compat.
                            { apply cond_pos. }
                            { assumption. }
                          }
                        }
                        {
                          apply Pdelta in t.
                          apply t.
                        }
                      }
                      {
                        assert (pr4 : forall c : R, x <= c <= x + h -> continuity_pt id c).
                        {
                          intros.
                          apply derivable_continuous.
                          apply derivable_id.
                        }
                        {
                          destruct (MVT (fn N) id x (x+h) pr1 pr2 xh_x pr3 pr4) as [c [P Hc]].
                          assert (Hc' : h * derive_pt (fn N) c (pr1 c P) = fn N (x+h) - fn N x).
                          {
                            pattern h at 1; replace h with (id (x + h) - id x).
                            2:{
                              unfold id.
                              unfold Rminus.
                              rewrite Rplus_comm.
                              rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
                              reflexivity.
                            }
                            rewrite <- Rmult_1_r.
                            replace R1 with (derive_pt id c (pr2 c P)).
                            2:{
                              clear.
                              unfold derivable_pt in pr2.
                              unfold derivable_pt_abs in pr2.
                              eapply uniqueness_limite.
                              2:apply derivable_pt_lim_id.
                              destruct (pr2 c P) as [l hl].
                              simpl.
                              apply hl.
                            }
                            { assumption. }
                          }
                          {
                            rewrite <- Hc'.
                            clear Hc Hc'.
                            replace (derive_pt (fn N) c (pr1 c P)) with (fn' N c).
                            {
                              replace (h * fn' N c - h * g x) with (h * (fn' N c - g x)).
                              2:{
                                unfold Rminus.
                                rewrite Ropp_mult_distr_r.
                                rewrite <- Rmult_plus_distr_l.
                                reflexivity.
                              }
                              rewrite Rabs_mult.
                              apply Rlt_trans with (Rabs h * eps / R4 + Rabs (f x - fn N x) + Rabs h * Rabs (fn' N c - g x)).
                              {
                                apply Rplus_lt_compat_r.
                                apply Rplus_lt_compat_r.
                                unfold R_dist in fnxh_CV_fxh.
                                rewrite Rabs_minus_sym.
                                apply fnxh_CV_fxh.
                                unfold N.
                                unfold ge.
                                rewrite <- plus_assoc.
                                apply Nat.le_add_r.
                              }
                              {
                                apply Rlt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * Rabs (fn' N c - g x)).
                                {
                                  apply Rplus_lt_compat_r.
                                  apply Rplus_lt_compat_l.
                                  unfold R_dist in fnx_CV_fx.
                                  rewrite Rabs_minus_sym.
                                  apply fnx_CV_fx.
                                  unfold N.
                                  unfold ge.
                                  rewrite (plus_comm _ N2).
                                  rewrite <- plus_assoc.
                                  apply Nat.le_add_r.
                                }
                                {
                                  replace (fn' N c - g x)  with ((fn' N c - g c) +  (g c - g x)).
                                  2:{
                                    unfold Rminus.
                                    repeat rewrite <- Rplus_assoc.
                                    apply Rplus_eq_compat_r.
                                    rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                                    reflexivity.
                                  }
                                  apply Rle_lt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * Rabs (fn' N c - g c) + Rabs h * Rabs (g c - g x)).
                                  {
                                    rewrite Rplus_assoc.
                                    rewrite Rplus_assoc.
                                    rewrite Rplus_assoc.
                                    apply Rplus_le_compat_l.
                                    apply Rplus_le_compat_l.
                                    rewrite <- Rmult_plus_distr_l.
                                    apply Rmult_le_compat_l.
                                    { apply Rabs_pos. }
                                    { apply Rabs_triang. }
                                  }
                                  {
                                    apply Rlt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * (eps / R8) + Rabs h * Rabs (g c - g x)).
                                    {
                                      apply Rplus_lt_compat_r.
                                      apply Rplus_lt_compat_l.
                                      apply Rmult_lt_compat_l.
                                      {
                                        apply Rabs_pos_lt.
                                        assumption.
                                      }
                                      {
                                        rewrite Rabs_minus_sym.
                                        apply fn'c_CVU_gc.
                                        {
                                          unfold N.
                                          rewrite plus_comm.
                                          apply Nat.le_add_r.
                                        }
                                        {
                                          assert (t : Boule x delta c).
                                          {
                                            destruct P.
                                            apply Rabs_def2 in xhinbxdelta.
                                            destruct xhinbxdelta.
                                            apply Rabs_def2 in xinb.
                                            apply Rabs_def1.
                                            {
                                              unfold Rminus.
                                              apply Rplus_lt_reg_r with (x+h).
                                              rewrite Rplus_assoc.
                                              rewrite (Rplus_comm delta).
                                              apply Rplus_lt_compat.
                                              { assumption. }
                                              {
                                                rewrite Rplus_comm.
                                                assumption.
                                              }
                                            }
                                            {
                                              unfold Rminus.
                                              apply Rplus_lt_reg_r with x.
                                              rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                                              rewrite Rplus_comm.
                                              apply Rplus_lt_reg_r with delta.
                                              rewrite Rplus_assoc, Rplus_opp_l.
                                              apply Rplus_lt_compat.
                                              { assumption. }
                                              { apply cond_pos. }
                                            }
                                          }
                                          {
                                            apply Pdelta in t.
                                            apply t.
                                          }
                                        }
                                      }
                                    }
                                    {
                                      apply Rlt_trans with (Rabs h * eps / R4 + Rabs h * eps / R4 + Rabs h * (eps / R8) + Rabs h * (eps / R8)).
                                      {
                                        rewrite Rplus_assoc.
                                        rewrite Rplus_assoc.
                                        rewrite Rplus_assoc.
                                        rewrite Rplus_assoc.
                                        apply Rplus_lt_compat_l.
                                        apply Rplus_lt_compat_l.
                                        rewrite <- Rmult_plus_distr_l.
                                        rewrite <- Rmult_plus_distr_l.
                                        apply Rmult_lt_compat_l.
                                        {
                                          apply Rabs_pos_lt.
                                          assumption.
                                        }
                                        {
                                          apply Rplus_lt_compat_l.
                                          simpl in g_cont.
                                          apply g_cont.
                                          split.
                                          {
                                            unfold D_x.
                                            split.
                                            {
                                              unfold no_cond.
                                              exact I.
                                            }
                                            {
                                              apply Rlt_not_eq.
                                              exact (proj1 P).
                                            }
                                          }
                                          {
                                            apply Rlt_trans with (Rabs h).
                                            {
                                              apply Rabs_def1.
                                              {
                                                destruct P.
                                                rewrite Rabs_pos_eq.
                                                {
                                                  unfold Rminus.
                                                  apply Rplus_lt_reg_r with x.
                                                  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_comm.
                                                  assumption.
                                                }
                                                {
                                                  left.
                                                  assumption.
                                                }
                                              }
                                              {
                                              apply Rle_lt_trans with R0.
                                              {
                                                assert (t := Rabs_pos h).
                                                clear -t.
                                                apply Ropp_le_cancel.
                                                rewrite Ropp_0, Ropp_involutive.
                                                assumption.
                                              }
                                              {
                                                clear -P.
                                                destruct P.
                                                unfold Rminus.
                                                apply Rplus_lt_reg_r with x.
                                                rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
                                                assumption.
                                              }
                                            }
                                          }
                                          {
                                            clear -Pdelta xhinbxdelta.
                                            apply Pdelta in xhinbxdelta.
                                            destruct xhinbxdelta as [_ P'].
                                            apply Rabs_def2 in P'.
                                            simpl in P'.
                                            destruct P'.
                                            apply Rabs_def1.
                                            {
                                              pattern h;rewrite <- Rplus_0_r.
                                              rewrite <- (Rplus_opp_l x).
                                              rewrite <- Rplus_assoc.
                                              rewrite Rplus_comm.
                                              rewrite <- Rplus_assoc.
                                              assumption.
                                            }
                                            {
                                              pattern h;rewrite <- Rplus_0_r.
                                              rewrite <- (Rplus_opp_l x).
                                              rewrite <- Rplus_assoc.
                                              rewrite Rplus_comm.
                                              rewrite <- Rplus_assoc.
                                              assumption.
                                            }
                                          }
                                        }
                                      }
                                    }
                                    {
                                      rewrite Rplus_assoc.
                                      rewrite Rplus_assoc.
                                      rewrite <- Rmult_plus_distr_l.
                                      replace (
                                        Rabs h * eps / R4 + (Rabs h * eps / R4 + Rabs h * (eps / R8 + eps / R8))
                                      ) with (
                                        Rabs h * (eps / R4 + eps / R4 + eps / R8 + eps / R8)
                                      ).
                                      2:{
                                        unfold Rdiv.
                                        repeat rewrite Rmult_assoc.
                                        repeat rewrite <- Rmult_plus_distr_l.
                                        repeat rewrite Rplus_assoc.
                                        reflexivity.
                                      }
                                      apply Rmult_lt_compat_l.
                                      {
                                         apply Rabs_pos_lt ; assumption.
                                      }
                                      {
                                        unfold Rdiv.
                                        replace R8 with (R2*R4).
                                        {
                                          rewrite Rinv_mult_distr.
                                          {
                                            repeat rewrite <- Rmult_assoc.
                                            repeat rewrite <- Rmult_plus_distr_r.
                                            pattern eps at 1;rewrite <- Rmult_1_r.
                                            pattern eps at 2;rewrite <- Rmult_1_r.
                                            pattern eps at 5;rewrite <- Rmult_1_r.
                                            repeat rewrite <- Rmult_plus_distr_l.
                                            rewrite Rmult_assoc.
                                            apply Rmult_lt_compat_l.
                                            { assumption. }
                                            {
                                              repeat rewrite Rplus_assoc.
                                              rewrite <- double.
                                              rewrite Rinv_r.
                                              {
                                                apply Rmult_lt_reg_r with R4.
                                                { exact Rlt_0_4. }
                                                {
                                                  rewrite Rmult_assoc.
                                                  rewrite Rinv_l, Rmult_1_l, Rmult_1_r.
                                                  {
                                                    unfold R4. unfold R2.
                                                    {
                                                      repeat rewrite Rplus_assoc.
                                                      repeat apply Rplus_lt_compat_l.
                                                      pattern R1 at 1;rewrite <- Rplus_0_l.
                                                      apply Rplus_lt_compat_r.
                                                      exact Rlt_0_1.
                                                  }
                                                }
                                                { apply Rlt_not_eq'. exact Rlt_0_4. }
                                              }
                                            }
                                            { exact Neq_2_0. }
                                          }
                                        }
                                        { exact Neq_2_0. }
                                        { apply Rlt_not_eq'. exact Rlt_0_4. }
                                      }
                                      {
rewrite double.
unfold R8.
reflexivity.
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                        {
                         assert (H := pr1 c P) ; elim H ; clear H ; intros l Hl.
                         assert (Temp : l = fn' N c).
                        {
                          assert (bc'rc : Boule c' r c).
                          {
                            assert (t : Boule x delta c).
                            {
                              clear - xhinbxdelta P.
                              destruct P.
                              apply Rabs_def2 in xhinbxdelta.
                              destruct xhinbxdelta.
                              apply Rabs_def1.
                              {
                                unfold Rminus.
                                apply Rplus_lt_reg_r with (x+h).
                                rewrite (Rplus_comm delta).
                                rewrite Rplus_assoc.
                                apply Rplus_lt_compat.
                                { assumption. }
                                {
                                  rewrite Rplus_comm.
                                  assumption.
                                }
                              }
                              {
                                unfold Rminus.
                                apply Rplus_lt_reg_r with x.
                                rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                                apply Rplus_lt_reg_l with delta.
                                rewrite <- Rplus_assoc, Rplus_opp_r.
                                apply Rplus_lt_compat.
                                { apply cond_pos. }
                                { assumption. }
                              }
                            }
                            apply Pdelta in t.
                            apply t.
                          }
                          assert (Hl' := Dfn_eq_fn' c N bc'rc).
                          unfold derivable_pt_abs in Hl.
                          clear -Hl Hl'.
                          apply uniqueness_limite with (f:= fn N) (x:=c).
                          { assumption. }
                          { assumption. }
                        }
                        rewrite <- Temp.
                        assert (Hl' : derivable_pt (fn N) c).
                        {
                          exists l.
                          apply Hl.
                        }
                        rewrite pr_nu_var with (g:= fn N) (pr2:=Hl').
                        {
                          elim Hl'.
                          clear Hl'.
                          intros l' Hl'.
                          assert (Main : l = l').
                          {
                            apply uniqueness_limite with (f:= fn N) (x:=c).
                            { assumption. }
                            { assumption. }
                          }
                          rewrite Main.
                          simpl.
                          reflexivity.
                        }
                        { reflexivity. }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  {
    replace ((f (x + h) - f x) / h - g x) with ((/h) * ((f (x + h) - f x) - h * g x)).
    {
      rewrite Rabs_mult.
      rewrite Rabs_Rinv.
      {
        replace eps with (/ Rabs h * (Rabs h * eps)).
        {
          apply Rmult_lt_compat_l.
          {
            apply Rinv_0_lt_compat.
            apply Rabs_pos_lt.
            assumption.
          }
          {
            replace (
              f (x + h) - f x - h * g x
            ) with (
              f (x + h) - fn N (x + h) - (f x - fn N x) + (fn N (x + h) - fn N x - h * g x)
            ).
            { assumption. }
            {
              unfold Rminus.
              repeat rewrite Rplus_assoc.
              apply Rplus_eq_compat_l.
              repeat rewrite <- Rplus_assoc.
              apply Rplus_eq_compat_r.
              rewrite Ropp_plus_distr.
              rewrite Ropp_involutive.
              repeat rewrite Rplus_assoc.
              rewrite (Rplus_comm (fn N x)).
              repeat rewrite Rplus_assoc.
              rewrite Rplus_opp_l, Rplus_0_r.
              rewrite Rplus_comm.
              repeat rewrite Rplus_assoc.
              rewrite Rplus_opp_r, Rplus_0_r.
              reflexivity.
            }
          }
        }
        {
          rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l.
          reflexivity.
          apply Rgt_not_eq.
          apply Rabs_pos_lt.
          assumption.
        }
      }
      { assumption. }
    }
    {
      unfold Rminus, Rdiv.
      rewrite Rmult_plus_distr_l.
      rewrite <- Ropp_mult_distr_r.
      repeat rewrite <- Rmult_assoc.
      rewrite Rinv_l, Rmult_1_l.
      2:assumption.
      apply Rplus_eq_compat_r.
      rewrite Rmult_comm.
      reflexivity.
    }
  }
}
}
}
Qed.