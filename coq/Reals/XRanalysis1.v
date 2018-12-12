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
Require Import XRfunctions.
Require Export XRlimit.
Require Export XRderiv.
Local Open Scope XR_scope.
Implicit Type f : R -> R.

(****************************************************)
(** *         Basic operations on functions         *)
(****************************************************)
Definition plus_fct f1 f2 (x:R) : R := f1 x + f2 x.
Definition opp_fct f (x:R) : R := - f x.
Definition mult_fct f1 f2 (x:R) : R := f1 x * f2 x.
Definition mult_real_fct (a:R) f (x:R) : R := a * f x.
Definition minus_fct f1 f2 (x:R) : R := f1 x - f2 x.
Definition div_fct f1 f2 (x:R) : R := f1 x / f2 x.
Definition div_real_fct (a:R) f (x:R) : R := a / f x.
Definition comp f1 f2 (x:R) : R := f1 (f2 x).
Definition inv_fct f (x:R) : R := / f x.

Delimit Scope Rfun_scope with F.

Arguments plus_fct (f1 f2)%F x%R.
Arguments mult_fct (f1 f2)%F x%R.
Arguments minus_fct (f1 f2)%F x%R.
Arguments div_fct (f1 f2)%F x%R.
Arguments inv_fct f%F x%R.
Arguments opp_fct f%F x%R.
Arguments mult_real_fct a%R f%F x%R.
Arguments div_real_fct a%R f%F x%R.
Arguments comp (f1 f2)%F x%R.

Infix "+" := plus_fct : Rfun_scope.
Notation "- x" := (opp_fct x) : Rfun_scope.
Infix "*" := mult_fct : Rfun_scope.
Infix "-" := minus_fct : Rfun_scope.
Infix "/" := div_fct : Rfun_scope.
Local Notation "f1 'o' f2" := (comp f1 f2)
  (at level 20, right associativity) : Rfun_scope.
Notation "/ x" := (inv_fct x) : Rfun_scope.

Definition fct_cte (a x:R) : R := a.
Definition id (x:R) := x.

(****************************************************)
(** *          Variations of functions              *)
(****************************************************)
Definition increasing f : Prop := forall x y:R, x <= y -> f x <= f y.
Definition decreasing f : Prop := forall x y:R, x <= y -> f y <= f x.
Definition strict_increasing f : Prop := forall x y:R, x < y -> f x < f y.
Definition strict_decreasing f : Prop := forall x y:R, x < y -> f y < f x.
Definition constant f : Prop := forall x y:R, f x = f y.

(**********)
Definition no_cond (x:R) : Prop := True.

(**********)
Definition constant_D_eq f (D:R -> Prop) (c:R) : Prop :=
  forall x:R, D x -> f x = c.

(***************************************************)
(** *    Definition of continuity as a limit       *)
(***************************************************)

(**********)
Definition continuity_pt f (x0:R) : Prop := continue_in f no_cond x0.
Definition continuity f : Prop := forall x:R, continuity_pt f x.

Arguments continuity_pt f%F x0%R.
Arguments continuity f%F.

Lemma continuity_pt_locally_ext :
  forall f g a x, R0 < a -> (forall y, R_dist y x < a -> f y = g y) ->
  continuity_pt f x -> continuity_pt g x.
intros f g a x a0 q cf eps ep.
destruct (cf eps ep) as [a' [a'p Pa']].
exists (Rmin a a'); split.
 unfold Rmin; destruct (Rle_dec a a').
  assumption.
 assumption.
intros y cy; rewrite <- !q.
  apply Pa'.
  split;[| apply Rlt_le_trans with (Rmin a a');[ | apply Rmin_r]];tauto.
 rewrite R_dist_eq; assumption.   
apply Rlt_le_trans with (Rmin a a');[ | apply Rmin_l]; tauto.
Qed.


(**********)
Lemma continuity_pt_plus :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 -> continuity_pt f2 x0 -> continuity_pt (f1 + f2) x0.
Proof.
  unfold continuity_pt, plus_fct; unfold continue_in; intros;
    apply limit_plus; assumption.
Qed.

Lemma continuity_pt_opp :
  forall f (x0:R), continuity_pt f x0 -> continuity_pt (- f) x0.
Proof.
  unfold continuity_pt, opp_fct; unfold continue_in; intros;
    apply limit_Ropp; assumption.
Qed.

Lemma continuity_pt_minus :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 -> continuity_pt f2 x0 -> continuity_pt (f1 - f2) x0.
Proof.
  unfold continuity_pt, minus_fct; unfold continue_in; intros;
    apply limit_minus; assumption.
Qed.

Lemma continuity_pt_mult :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 -> continuity_pt f2 x0 -> continuity_pt (f1 * f2) x0.
Proof.
  unfold continuity_pt, mult_fct; unfold continue_in; intros;
    apply limit_mul; assumption.
Qed.

Lemma continuity_pt_const : forall f (x0:R), constant f -> continuity_pt f x0.
Proof.
  unfold constant, continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      intros; exists R1; split;
        [ apply Rlt_0_1
          | intros; generalize (H x x0); intro; rewrite H2; simpl;
            rewrite R_dist_eq; assumption ].
Qed.

Lemma continuity_pt_scal :
  forall f (a x0:R),
    continuity_pt f x0 -> continuity_pt (mult_real_fct a f) x0.
Proof.
  unfold continuity_pt, mult_real_fct; unfold continue_in;
    intros; apply (limit_mul (fun x:R => a) f (D_x no_cond x0) a (f x0) x0).
  unfold limit1_in; unfold limit_in; intros; exists R1; split.
  apply Rlt_0_1.
  intros; rewrite R_dist_eq; assumption.
  assumption.
Qed.

Lemma continuity_pt_inv :
  forall f (x0:R), continuity_pt f x0 -> f x0 <> R0 -> continuity_pt (/ f) x0.
Proof.
  intros.
  replace (/ f)%F with (fun x:R => / f x).
  unfold continuity_pt; unfold continue_in; intros;
    apply limit_inv; assumption.
  unfold inv_fct; reflexivity.
Qed.

Lemma div_eq_inv : forall f1 f2, (f1 / f2)%F = (f1 * / f2)%F.
Proof.
  intros; reflexivity.
Qed.

Lemma continuity_pt_div :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 ->
    continuity_pt f2 x0 -> f2 x0 <> R0 -> continuity_pt (f1 / f2) x0.
Proof.
  intros; rewrite (div_eq_inv f1 f2); apply continuity_pt_mult;
    [ assumption | apply continuity_pt_inv; assumption ].
Qed.

Lemma continuity_pt_comp :
  forall f1 f2 (x:R),
    continuity_pt f1 x -> continuity_pt f2 (f1 x) -> continuity_pt (f2 o f1) x.
Proof.
  unfold continuity_pt; unfold continue_in; intros;
    unfold comp.
  cut
    (limit1_in (fun x0:R => f2 (f1 x0))
      (Dgf (D_x no_cond x) (D_x no_cond (f1 x)) f1) (
        f2 (f1 x)) x ->
      limit1_in (fun x0:R => f2 (f1 x0)) (D_x no_cond x) (f2 (f1 x)) x).
  intro; apply H1.
  eapply limit_comp.
  apply H.
  apply H0.
  unfold limit1_in; unfold limit_in; unfold dist;
    simpl; unfold R_dist; intros.
  assert (H3 := H1 eps H2).
  elim H3; intros.
  exists x0.
  split.
  elim H4; intros; assumption.
  intros; case (Req_dec (f1 x) (f1 x1)); intro.
  rewrite H6; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  elim H4; intros; apply H8.
  split.
  unfold Dgf, D_x, no_cond.
  split.
  split.
  trivial.
  elim H5; unfold D_x, no_cond; intros.
  elim H9; intros; assumption.
  split.
  trivial.
  assumption.
  elim H5; intros; assumption.
Qed.

(**********)
Lemma continuity_plus :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f1 + f2).
Proof.
  unfold continuity; intros;
    apply (continuity_pt_plus f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_opp : forall f, continuity f -> continuity (- f).
Proof.
  unfold continuity; intros; apply (continuity_pt_opp f x (H x)).
Qed.

Lemma continuity_minus :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f1 - f2).
Proof.
  unfold continuity; intros;
    apply (continuity_pt_minus f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_mult :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f1 * f2).
Proof.
  unfold continuity; intros;
    apply (continuity_pt_mult f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_const : forall f, constant f -> continuity f.
Proof.
  unfold continuity; intros; apply (continuity_pt_const f x H).
Qed.

Lemma continuity_scal :
  forall f (a:R), continuity f -> continuity (mult_real_fct a f).
Proof.
  unfold continuity; intros; apply (continuity_pt_scal f a x (H x)).
Qed.

Lemma continuity_inv :
  forall f, continuity f -> (forall x:R, f x <> R0) -> continuity (/ f).
Proof.
  unfold continuity; intros; apply (continuity_pt_inv f x (H x) (H0 x)).
Qed.

Lemma continuity_div :
  forall f1 f2,
    continuity f1 ->
    continuity f2 -> (forall x:R, f2 x <> R0) -> continuity (f1 / f2).
Proof.
  unfold continuity; intros;
    apply (continuity_pt_div f1 f2 x (H x) (H0 x) (H1 x)).
Qed.

Lemma continuity_comp :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f2 o f1).
Proof.
  unfold continuity; intros.
  apply (continuity_pt_comp f1 f2 x (H x) (H0 (f1 x))).
Qed.


(*****************************************************)
(** * Derivative's definition using Landau's kernel  *)
(*****************************************************)

Definition derivable_pt_lim f (x l:R) : Prop :=
  forall eps:R,
    R0 < eps ->
    exists delta : posreal,
      (forall h:R,
        h <> R0 -> Rabs h < delta -> Rabs ((f (x + h) - f x) / h - l) < eps).

Definition derivable_pt_abs f (x l:R) : Prop := derivable_pt_lim f x l.

Definition derivable_pt f (x:R) := { l:R | derivable_pt_abs f x l }.
Definition derivable f := forall x:R, derivable_pt f x.

Definition derive_pt f (x:R) (pr:derivable_pt f x) := proj1_sig pr.
Definition derive f (pr:derivable f) (x:R) := derive_pt f x (pr x).

Arguments derivable_pt_lim f%F x%R l.
Arguments derivable_pt_abs f%F (x l)%R.
Arguments derivable_pt f%F x%R.
Arguments derivable f%F.
Arguments derive_pt f%F x%R pr.
Arguments derive f%F pr x.

Definition antiderivative f (g:R -> R) (a b:R) : Prop :=
  (forall x:R,
    a <= x <= b ->  exists pr : derivable_pt g x, f x = derive_pt g x pr) /\
  a <= b.
(**************************************)
(** * Class of differential functions *)
(**************************************)
Record Differential : Type := mkDifferential
  {d1 :> R -> R; cond_diff : derivable d1}.

Record Differential_D2 : Type := mkDifferential_D2
  {d2 :> R -> R;
    cond_D1 : derivable d2;
    cond_D2 : derivable (derive d2 cond_D1)}.

(**********)
Lemma uniqueness_step1 :
  forall f (x l1 l2:R),
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> R0) l1 R0 ->
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> R0) l2 R0 ->
    l1 = l2.
Proof.
  intros;
    apply
      (single_limit (fun h:R => (f (x + h) - f x) / h) (
        fun h:R => h <> R0) l1 l2 R0); try assumption.
  unfold adhDa; intros; exists (alp / R2).
  split.
  unfold Rdiv; apply prod_neq_R0.
  red; intro; rewrite H2 in H1; elim (Rlt_irrefl _ H1).
  apply Rinv_neq_0_compat. exact Neq_2_0.
  unfold R_dist; unfold Rminus; rewrite Ropp_0;
    rewrite Rplus_0_r; unfold Rdiv; rewrite Rabs_mult.
  replace (Rabs (/ R2)) with (/ R2).
  replace (Rabs alp) with alp.
  apply Rmult_lt_reg_l with R2.
  exact Rlt_0_2.
  rewrite (Rmult_comm R2); rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
2:{
exact Neq_2_0.
}
 rewrite Rmult_1_r; rewrite double;
      pattern alp at 1; replace alp with (alp + R0).
2:{
rewrite Rplus_0_r. reflexivity.
}
 apply Rplus_lt_compat_l; assumption.
  symmetry ; apply Rabs_right; left; assumption.
  symmetry ; apply Rabs_right; left; change (R0 < / R2);
    apply Rinv_0_lt_compat.
exact Rlt_0_2.
Qed.

Lemma uniqueness_step2 :
  forall f (x l:R),
    derivable_pt_lim f x l ->
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> R0) l R0.
Proof.
  unfold derivable_pt_lim; intros; unfold limit1_in;
    unfold limit_in; intros.
  assert (H1 := H eps H0).
  elim H1; intros.
  exists (pos x0).
  split.
  apply (cond_pos x0).
  simpl; unfold R_dist; intros.
  elim H3; intros.
  apply H2;
    [ assumption
      | unfold Rminus in H5; rewrite Ropp_0 in H5; rewrite Rplus_0_r in H5;
        assumption ].
Qed.

Lemma uniqueness_step3 :
  forall f (x l:R),
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> R0) l R0 ->
    derivable_pt_lim f x l.
Proof.
  unfold limit1_in, derivable_pt_lim; unfold limit_in;
    unfold dist; simpl; intros.
  elim (H eps H0).
  intros; elim H1; intros.
  exists (mkposreal x0 H2).
  simpl; intros; unfold R_dist in H3; apply (H3 h).
  split;
    [ assumption
      | unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r; assumption ].
Qed.

Lemma uniqueness_limite :
  forall f (x l1 l2:R),
    derivable_pt_lim f x l1 -> derivable_pt_lim f x l2 -> l1 = l2.
Proof.
  intros.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  assert (H3 := uniqueness_step1 _ _ _ _ H1 H2).
  assumption.
Qed.

Lemma derive_pt_eq :
  forall f (x l:R) (pr:derivable_pt f x),
    derive_pt f x pr = l <-> derivable_pt_lim f x l.
Proof.
  intros; split.
  intro; assert (H1 := proj2_sig pr); unfold derive_pt in H; rewrite H in H1;
    assumption.
  intro; assert (H1 := proj2_sig pr); unfold derivable_pt_abs in H1.
  assert (H2 := uniqueness_limite _ _ _ _ H H1).
  unfold derive_pt; unfold derivable_pt_abs.
  symmetry ; assumption.
Qed.

(**********)
Lemma derive_pt_eq_0 :
  forall f (x l:R) (pr:derivable_pt f x),
    derivable_pt_lim f x l -> derive_pt f x pr = l.
Proof.
  intros; elim (derive_pt_eq f x l pr); intros.
  apply (H1 H).
Qed.

(**********)
Lemma derive_pt_eq_1 :
  forall f (x l:R) (pr:derivable_pt f x),
    derive_pt f x pr = l -> derivable_pt_lim f x l.
Proof.
  intros; elim (derive_pt_eq f x l pr); intros.
  apply (H0 H).
Qed.


(**********************************************************************)
(** * Equivalence of this definition with the one using limit concept *)
(**********************************************************************)
Lemma derive_pt_D_in :
  forall f (df:R -> R) (x:R) (pr:derivable_pt f x),
    D_in f df no_cond x <-> derive_pt f x pr = df x.
Proof.
  intros; split.
  unfold D_in; unfold limit1_in; unfold limit_in;
    simpl; unfold R_dist; intros.
  apply derive_pt_eq_0.
  unfold derivable_pt_lim.
  intros; elim (H eps H0); intros alpha H1; elim H1; intros;
    exists (mkposreal alpha H2); intros; generalize (H3 (x + h));
      intro; cut (x + h - x = h).
        intro; cut (D_x no_cond x (x + h) /\ Rabs (x + h - x) < alpha).
          intro; generalize (H6 H8); rewrite H7; intro; assumption.
            split.
               unfold D_x; split.
                 unfold no_cond; trivial.
                   apply Rminus_not_eq_right; rewrite H7; assumption .
                 rewrite H7; assumption.
          unfold Rminus. rewrite Rplus_comm. rewrite <- Rplus_assoc.
rewrite Rplus_opp_l. rewrite Rplus_0_l. reflexivity.
  intro.
  assert (H0 := derive_pt_eq_1 f x (df x) pr H).
  unfold D_in; unfold limit1_in; unfold limit_in;
    unfold dist; simpl; unfold R_dist;
      intros.
  elim (H0 eps H1); intros alpha H2; exists (pos alpha); split.
  apply (cond_pos alpha).
  intros; elim H3; intros; unfold D_x in H4; elim H4; intros; cut (x0 - x <> R0).
  intro; generalize (H2 (x0 - x) H8 H5); replace (x + (x0 - x)) with x0.
  intro; assumption.
unfold Rminus. rewrite Rplus_comm. rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
reflexivity.
intro eq. apply H7. apply Rplus_eq_reg_r with (-x). rewrite Rplus_opp_r.
symmetry. exact eq.
Qed.

Lemma derivable_pt_lim_D_in :
  forall f (df:R -> R) (x:R),
    D_in f df no_cond x <-> derivable_pt_lim f x (df x).
Proof.
  intros; split.
  unfold D_in; unfold limit1_in; unfold limit_in;
    simpl; unfold R_dist; intros.
  unfold derivable_pt_lim.
  intros; elim (H eps H0); intros alpha H1; elim H1; intros;
    exists (mkposreal alpha H2); intros; generalize (H3 (x + h));
      intro; cut (x + h - x = h).
         intro; cut (D_x no_cond x (x + h) /\ Rabs (x + h - x) < alpha).
           intro; generalize (H6 H8); rewrite H7; intro; assumption.
             split.
               unfold D_x; split.
                 unfold no_cond; trivial.
                  apply Rminus_not_eq_right; rewrite H7; assumption.
                rewrite H7; assumption.
          unfold Rminus. rewrite Rplus_comm. rewrite <- Rplus_assoc.
rewrite Rplus_opp_l. rewrite Rplus_0_l. reflexivity.
  intro.
  unfold derivable_pt_lim in H.
  unfold D_in; unfold limit1_in; unfold limit_in;
    unfold dist; simpl; unfold R_dist;
      intros.
  elim (H eps H0); intros alpha H2; exists (pos alpha); split.
  apply (cond_pos alpha).
  intros.
  elim H1; intros; unfold D_x in H3; elim H3; intros; cut (x0 - x <> R0).
  intro; generalize (H2 (x0 - x) H7 H4); replace (x + (x0 - x)) with x0.
  intro; assumption.
  unfold Rminus. rewrite Rplus_comm. rewrite Rplus_assoc. rewrite Rplus_opp_l.
rewrite Rplus_0_r. reflexivity.
intro eq. apply H6.
apply Rplus_eq_reg_r with (-x).
rewrite Rplus_opp_r. symmetry. exact eq.
Qed.

(* Extensionally equal functions have the same derivative. *)

Lemma derivable_pt_lim_ext : forall f g x l, (forall z, f z = g z) -> 
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
intros f g x l fg df e ep; destruct (df e ep) as [d pd]; exists d; intros h;
rewrite <- !fg; apply pd.
Qed.

(* extensionally equal functions have the same derivative, locally. *)

Lemma derivable_pt_lim_locally_ext : forall f g x a b l, 
  a < x < b ->
  (forall z, a < z < b -> f z = g z) ->
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
intros f g x a b l axb fg df e ep.
destruct (df e ep) as [d pd].
assert (d'h : R0 < Rmin d (Rmin (b - x) (x - a))).
{
 apply Rmin_pos.
apply cond_pos.
apply Rmin_pos.
apply Rlt_0_minus. apply axb.
apply Rlt_0_minus. apply axb.
}
exists (mkposreal _ d'h); simpl; intros h hn0 cmp.
rewrite <- !fg;[ |assumption | ].
  apply pd;[assumption |].
 apply Rlt_le_trans with (1 := cmp), Rmin_l.
assert (-h < x - a).
 apply Rle_lt_trans with (1 := Rle_abs _).
 rewrite Rabs_Ropp; apply Rlt_le_trans with (1 := cmp).
 rewrite Rmin_assoc; apply Rmin_r.
assert (h < b - x).
 apply Rle_lt_trans with (1 := Rle_abs _).
 apply Rlt_le_trans with (1 := cmp).
 rewrite Rmin_comm, <- Rmin_assoc; apply Rmin_l.
split.
 apply (Rplus_lt_reg_l (- h)).
 replace ((-h) + (x + h)) with x.
2:{
rewrite Rplus_comm. rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity.
}
 apply (Rplus_lt_reg_r (- a)).
 replace (((-h) + a) + - a) with (-h).
2:{
rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r. reflexivity.
}
 assumption.
apply (Rplus_lt_reg_r (- x)).
replace (x + h + - x) with h.
2:{
rewrite Rplus_comm. rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l. reflexivity.
}
assumption.
Qed.


(***********************************)
(** * derivability -> continuity   *)
(***********************************)
(**********)
Lemma derivable_derive :
  forall f (x:R) (pr:derivable_pt f x),  exists l : R, derive_pt f x pr = l.
Proof.
  intros; exists (proj1_sig pr).
  unfold derive_pt; reflexivity.
Qed.

Theorem derivable_continuous_pt :
  forall f (x:R), derivable_pt f x -> continuity_pt f x.
Proof.
  intros f x X.
  generalize (derivable_derive f x X); intro.
  elim H; intros l H1.
  cut (l = fct_cte l x).
  intro.
  rewrite H0 in H1.
  generalize (derive_pt_D_in f (fct_cte l) x); intro.
  elim (H2 X); intros.
  generalize (H4 H1); intro.
  unfold continuity_pt.
  apply (cont_deriv f (fct_cte l) no_cond x H5).
  unfold fct_cte; reflexivity.
Qed.

Theorem derivable_continuous : forall f, derivable f -> continuity f.
Proof.
  unfold derivable, continuity; intros f X x.
  apply (derivable_continuous_pt f x (X x)).
Qed.

(****************************************************************)
(** *                    Main rules                             *)
(****************************************************************)

Lemma derivable_pt_lim_plus :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 -> derivable_pt_lim (f1 + f2) x (l1 + l2).
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  unfold plus_fct.
  cut
    (forall h:R,
      (f1 (x + h) + f2 (x + h) - (f1 x + f2 x)) / h =
      (f1 (x + h) - f1 x) / h + (f2 (x + h) - f2 x) / h).
  intro.
  generalize
    (limit_plus (fun h':R => (f1 (x + h') - f1 x) / h')
      (fun h':R => (f2 (x + h') - f2 x) / h') (fun h:R => h <> R0) l1 l2 R0 H1 H2).
  unfold limit1_in; unfold limit_in; unfold dist;
    simpl; unfold R_dist; intros.
  elim (H4 eps H5); intros.
  exists x0.
  elim H6; intros.
  split.
  assumption.
  intros; rewrite H3; apply H8; assumption.
  intro; unfold Rdiv.
unfold Rminus.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Ropp_plus_distr.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
rewrite Rplus_comm.
reflexivity.
Qed.

Lemma derivable_pt_lim_opp :
  forall f (x l:R), derivable_pt_lim f x l -> derivable_pt_lim (- f) x (- l).
Proof.
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  unfold opp_fct.
  cut (forall h:R, (- f (x + h) - - f x) / h = - ((f (x + h) - f x) / h)).
  intro.
  generalize
    (limit_Ropp (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> R0) l R0 H1).
  unfold limit1_in; unfold limit_in; unfold dist;
    simpl; unfold R_dist; intros.
  elim (H2 eps H3); intros.
  exists x0.
  elim H4; intros.
  split.
  assumption.
  intros; rewrite H0; apply H6; assumption.
  intro; unfold Rdiv.
unfold Rminus.
rewrite Ropp_involutive.
rewrite Ropp_mult_distr_l.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
reflexivity.
Qed.

Lemma derivable_pt_lim_minus :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 -> derivable_pt_lim (f1 - f2) x (l1 - l2).
Proof.
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  unfold minus_fct.
  cut
    (forall h:R,
      (f1 (x + h) - f1 x) / h - (f2 (x + h) - f2 x) / h =
      (f1 (x + h) - f2 (x + h) - (f1 x - f2 x)) / h).
  intro.
  generalize
    (limit_minus (fun h':R => (f1 (x + h') - f1 x) / h')
      (fun h':R => (f2 (x + h') - f2 x) / h') (fun h:R => h <> R0) l1 l2 R0 H1 H2).
  unfold limit1_in; unfold limit_in; unfold dist;
    simpl; unfold R_dist; intros.
  elim (H4 eps H5); intros.
  exists x0.
  elim H6; intros.
  split.
  assumption.
  intros; rewrite <- H3; apply H8; assumption.
  intro; unfold Rdiv.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
apply Rmult_eq_compat_r.
repeat rewrite Ropp_plus_distr.
repeat rewrite Ropp_involutive.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
repeat rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
rewrite Rplus_comm.
reflexivity.
Qed.

Lemma derivable_pt_lim_mult :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 ->
    derivable_pt_lim (f1 * f2) x (l1 * f2 x + f1 x * l2).
Proof.
  intros.
  assert (H1 := derivable_pt_lim_D_in f1 (fun y:R => l1) x).
  elim H1; intros.
  assert (H4 := H3 H).
  assert (H5 := derivable_pt_lim_D_in f2 (fun y:R => l2) x).
  elim H5; intros.
  assert (H8 := H7 H0).
  clear H1 H2 H3 H5 H6 H7.
  assert
    (H1 :=
      derivable_pt_lim_D_in (f1 * f2)%F (fun y:R => l1 * f2 x + f1 x * l2) x).
  elim H1; intros.
  clear H1 H3.
  apply H2.
  unfold mult_fct.
  apply (Dmult no_cond (fun y:R => l1) (fun y:R => l2) f1 f2 x); assumption.
Qed.

Lemma derivable_pt_lim_const : forall a x:R, derivable_pt_lim (fct_cte a) x R0.
Proof.
  intros; unfold fct_cte, derivable_pt_lim.
  intros; exists (mkposreal R1 Rlt_0_1); intros; unfold Rminus;
    rewrite Rplus_opp_r; unfold Rdiv; rewrite Rmult_0_l;
      rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
Qed.

Lemma derivable_pt_lim_scal :
  forall f (a x l:R),
    derivable_pt_lim f x l -> derivable_pt_lim (mult_real_fct a f) x (a * l).
Proof.
  intros.
  assert (H0 := derivable_pt_lim_const a x).
  replace (mult_real_fct a f) with (fct_cte a * f)%F.
  replace (a * l) with (R0 * f x + a * l).
2:{
rewrite Rmult_0_l. rewrite Rplus_0_l. reflexivity. }
  apply (derivable_pt_lim_mult (fct_cte a) f x R0 l); assumption.
  unfold mult_real_fct, mult_fct, fct_cte; reflexivity.
Qed.

Lemma derivable_pt_lim_div_scal :
  forall f x l a, derivable_pt_lim f x l ->
     derivable_pt_lim (fun y => f y / a) x (l / a).
intros f x l a df;
  apply (derivable_pt_lim_ext (fun y => /a * f y)).
 intros z; rewrite Rmult_comm; reflexivity.
unfold Rdiv; rewrite Rmult_comm; apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derivable_pt_lim_scal_right :
  forall f x l a, derivable_pt_lim f x l ->
     derivable_pt_lim (fun y => f y * a) x (l * a).
intros f x l a df;
  apply (derivable_pt_lim_ext (fun y => a * f y)).
 intros z; rewrite Rmult_comm; reflexivity.
unfold Rdiv; rewrite Rmult_comm; apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derivable_pt_lim_id : forall x:R, derivable_pt_lim id x R1.
Proof.
  intro; unfold derivable_pt_lim.
  intros eps Heps; exists (mkposreal eps Heps); intros h H1 H2;
    unfold id; replace ((x + h - x) / h - R1) with R0.
  rewrite Rabs_R0; apply Rle_lt_trans with (Rabs h).
  apply Rabs_pos.
  assumption.
  unfold Rminus; rewrite Rplus_assoc; rewrite (Rplus_comm x);
    rewrite Rplus_assoc.
  rewrite Rplus_opp_l; rewrite Rplus_0_r; unfold Rdiv;
    rewrite <- Rinv_r_sym.
  symmetry ; apply Rplus_opp_r.
  assumption.
Qed.

Lemma derivable_pt_lim_Rsqr : forall x:R, derivable_pt_lim Rsqr x (R2 * x).
Proof.
  intro; unfold derivable_pt_lim.
  unfold Rsqr; intros eps Heps; exists (mkposreal eps Heps);
    intros h H1 H2; replace (((x + h) * (x + h) - x * x) / h - R2 * x) with h.
  assumption.
  replace ((x + h) * (x + h) - x * x) with (R2 * x * h + h * h).
2:{
unfold R2.
unfold Rminus.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
symmetry.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_eq_compat_r.
rewrite Rmult_comm.
reflexivity.
}
  unfold Rdiv; rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite <- Rinv_r_sym; [ idtac | assumption ].
repeat rewrite Rmult_1_r.
unfold Rminus. rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
reflexivity.
Qed.

Lemma derivable_pt_lim_comp :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 (f1 x) l2 -> derivable_pt_lim (f2 o f1) x (l2 * l1).
Proof.
  intros; assert (H1 := derivable_pt_lim_D_in f1 (fun y:R => l1) x).
  elim H1; intros.
  assert (H4 := H3 H).
  assert (H5 := derivable_pt_lim_D_in f2 (fun y:R => l2) (f1 x)).
  elim H5; intros.
  assert (H8 := H7 H0).
  clear H1 H2 H3 H5 H6 H7.
  assert (H1 := derivable_pt_lim_D_in (f2 o f1)%F (fun y:R => l2 * l1) x).
  elim H1; intros.
  clear H1 H3; apply H2.
  unfold comp;
    cut
      (D_in (fun x0:R => f2 (f1 x0)) (fun y:R => l2 * l1)
        (Dgf no_cond no_cond f1) x ->
        D_in (fun x0:R => f2 (f1 x0)) (fun y:R => l2 * l1) no_cond x).
  intro; apply H1.
  rewrite Rmult_comm;
    apply (Dcomp no_cond no_cond (fun y:R => l1) (fun y:R => l2) f1 f2 x);
      assumption.
  unfold Dgf, D_in, no_cond; unfold limit1_in;
    unfold limit_in; unfold dist; simpl;
      unfold R_dist; intros.
  elim (H1 eps H3); intros.
  exists x0; intros; split.
  elim H5; intros; assumption.
  intros; elim H5; intros; apply H9; split.
  unfold D_x; split.
  split; trivial.
  elim H6; intros; unfold D_x in H10; elim H10; intros; assumption.
  elim H6; intros; assumption.
Qed.

Lemma derivable_pt_plus :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 + f2) x.
Proof.
  unfold derivable_pt; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 + x1).
  apply derivable_pt_lim_plus; assumption.
Qed.

Lemma derivable_pt_opp :
  forall f (x:R), derivable_pt f x -> derivable_pt (- f) x.
Proof.
  unfold derivable_pt; intros f x X.
  elim X; intros.
  exists (- x0).
  apply derivable_pt_lim_opp; assumption.
Qed.

Lemma derivable_pt_minus :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 - f2) x.
Proof.
  unfold derivable_pt; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 - x1).
  apply derivable_pt_lim_minus; assumption.
Qed.

Lemma derivable_pt_mult :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 * f2) x.
Proof.
  unfold derivable_pt; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 * f2 x + f1 x * x1).
  apply derivable_pt_lim_mult; assumption.
Qed.

Lemma derivable_pt_const : forall a x:R, derivable_pt (fct_cte a) x.
Proof.
  intros; unfold derivable_pt.
  exists R0.
  apply derivable_pt_lim_const.
Qed.

Lemma derivable_pt_scal :
  forall f (a x:R), derivable_pt f x -> derivable_pt (mult_real_fct a f) x.
Proof.
  unfold derivable_pt; intros f1 a x X.
  elim X; intros.
  exists (a * x0).
  apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derivable_pt_id : forall x:R, derivable_pt id x.
Proof.
  unfold derivable_pt; intro.
  exists R1.
  apply derivable_pt_lim_id.
Qed.

Lemma derivable_pt_Rsqr : forall x:R, derivable_pt Rsqr x.
Proof.
  unfold derivable_pt; intro; exists (R2 * x).
  apply derivable_pt_lim_Rsqr.
Qed.

Lemma derivable_pt_comp :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 (f1 x) -> derivable_pt (f2 o f1) x.
Proof.
  unfold derivable_pt; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x1 * x0).
  apply derivable_pt_lim_comp; assumption.
Qed.

Lemma derivable_plus :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f1 + f2).
Proof.
  unfold derivable; intros f1 f2 X X0 x.
  apply (derivable_pt_plus _ _ x (X _) (X0 _)).
Qed.

Lemma derivable_opp : forall f, derivable f -> derivable (- f).
Proof.
  unfold derivable; intros f X x.
  apply (derivable_pt_opp _ x (X _)).
Qed.

Lemma derivable_minus :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f1 - f2).
Proof.
  unfold derivable; intros f1 f2 X X0 x.
  apply (derivable_pt_minus _ _ x (X _) (X0 _)).
Qed.

Lemma derivable_mult :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f1 * f2).
Proof.
  unfold derivable; intros f1 f2 X X0 x.
  apply (derivable_pt_mult _ _ x (X _) (X0 _)).
Qed.

Lemma derivable_const : forall a:R, derivable (fct_cte a).
Proof.
  unfold derivable; intros.
  apply derivable_pt_const.
Qed.

Lemma derivable_scal :
  forall f (a:R), derivable f -> derivable (mult_real_fct a f).
Proof.
  unfold derivable; intros f a X x.
  apply (derivable_pt_scal _ a x (X _)).
Qed.

Lemma derivable_id : derivable id.
Proof.
  unfold derivable; intro; apply derivable_pt_id.
Qed.

Lemma derivable_Rsqr : derivable Rsqr.
Proof.
  unfold derivable; intro; apply derivable_pt_Rsqr.
Qed.

Lemma derivable_comp :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f2 o f1).
Proof.
  unfold derivable; intros f1 f2 X X0 x.
  apply (derivable_pt_comp _ _ x (X _) (X0 _)).
Qed.

Lemma derive_pt_plus :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 x),
    derive_pt (f1 + f2) x (derivable_pt_plus _ _ _ pr1 pr2) =
    derive_pt f1 x pr1 + derive_pt f2 x pr2.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 + f2)%F x (derivable_pt_plus _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_plus; assumption.
Qed.

Lemma derive_pt_opp :
  forall f (x:R) (pr1:derivable_pt f x),
    derive_pt (- f) x (derivable_pt_opp _ _ pr1) = - derive_pt f x pr1.
Proof.
  intros.
  assert (H := derivable_derive f x pr1).
  assert (H0 := derivable_derive (- f)%F x (derivable_pt_opp _ _ pr1)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  rewrite H; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  apply derivable_pt_lim_opp; assumption.
Qed.

Lemma derive_pt_minus :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 x),
    derive_pt (f1 - f2) x (derivable_pt_minus _ _ _ pr1 pr2) =
    derive_pt f1 x pr1 - derive_pt f2 x pr2.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 - f2)%F x (derivable_pt_minus _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_minus; assumption.
Qed.

Lemma derive_pt_mult :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 x),
    derive_pt (f1 * f2) x (derivable_pt_mult _ _ _ pr1 pr2) =
    derive_pt f1 x pr1 * f2 x + f1 x * derive_pt f2 x pr2.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 * f2)%F x (derivable_pt_mult _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_mult; assumption.
Qed.

Lemma derive_pt_const :
  forall a x:R, derive_pt (fct_cte a) x (derivable_pt_const a x) = R0.
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_const.
Qed.

Lemma derive_pt_scal :
  forall f (a x:R) (pr:derivable_pt f x),
    derive_pt (mult_real_fct a f) x (derivable_pt_scal _ _ _ pr) =
    a * derive_pt f x pr.
Proof.
  intros.
  assert (H := derivable_derive f x pr).
  assert
    (H0 := derivable_derive (mult_real_fct a f) x (derivable_pt_scal _ _ _ pr)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  rewrite H; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr).
  unfold derive_pt in H; rewrite H in H3.
  apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derive_pt_id : forall x:R, derive_pt id x (derivable_pt_id _) = R1.
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_id.
Qed.

Lemma derive_pt_Rsqr :
  forall x:R, derive_pt Rsqr x (derivable_pt_Rsqr _) = R2 * x.
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_Rsqr.
Qed.

Lemma derive_pt_comp :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 (f1 x)),
    derive_pt (f2 o f1) x (derivable_pt_comp _ _ _ pr1 pr2) =
    derive_pt f2 (f1 x) pr2 * derive_pt f1 x pr1.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 (f1 x) pr2).
  assert
    (H1 := derivable_derive (f2 o f1)%F x (derivable_pt_comp _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_comp; assumption.
Qed.

(* Pow *)
Definition pow_fct (n:nat) (y:R) : R := y ^ n.

Lemma derivable_pt_lim_pow_pos :
  forall (x:R) (n:nat),
    (0 < n)%nat -> derivable_pt_lim (fun y:R => y ^ n) x (INR n * x ^ pred n).
Proof.
  intros.
  induction  n as [| n Hrecn].
  elim (lt_irrefl _ H).
  cut (n = 0%nat \/ (0 < n)%nat).
  intro; elim H0; intro.
  rewrite H1; simpl.
  replace (fun y:R => y * R1) with (id * fct_cte R1)%F.
  replace (R1 * R1) with (R1 * fct_cte R1 x + id x * R0).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte, id.
rewrite Rmult_0_r. rewrite Rplus_0_r. reflexivity.
  reflexivity.
  replace (fun y:R => y ^ S n) with (fun y:R => y * y ^ n).
  replace (pred (S n)) with n; [ idtac | reflexivity ].
  replace (fun y:R => y * y ^ n) with (id * (fun y:R => y ^ n))%F.
  set (f := fun y:R => y ^ n).
  replace (INR (S n) * x ^ n) with (R1 * f x + id x * (INR n * x ^ pred n)).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_id.
  unfold f; apply Hrecn; assumption.
  unfold f.
  pattern n at 1 5; replace n with (S (pred n)).
  unfold id; rewrite S_INR; simpl.
{
rewrite Rmult_1_l.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Rmult_assoc.
apply Rmult_eq_compat_r.
rewrite Rmult_comm.
reflexivity.
}
  symmetry ; apply S_pred with 0%nat; assumption.
  unfold mult_fct, id; reflexivity.
  reflexivity.
  inversion H.
  left; reflexivity.
  right.
  apply lt_le_trans with 1%nat.
  apply lt_O_Sn.
  assumption.
Qed.

Lemma derivable_pt_lim_pow :
  forall (x:R) (n:nat),
    derivable_pt_lim (fun y:R => y ^ n) x (INR n * x ^ pred n).
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl.
  rewrite Rmult_0_l.
  replace (fun _:R => R1) with (fct_cte R1);
  [ apply derivable_pt_lim_const | reflexivity ].
  apply derivable_pt_lim_pow_pos.
  apply lt_O_Sn.
Qed.

Lemma derivable_pt_pow :
  forall (n:nat) (x:R), derivable_pt (fun y:R => y ^ n) x.
Proof.
  intros; unfold derivable_pt.
  exists (INR n * x ^ pred n).
  apply derivable_pt_lim_pow.
Qed.

Lemma derivable_pow : forall n:nat, derivable (fun y:R => y ^ n).
Proof.
  intro; unfold derivable; intro; apply derivable_pt_pow.
Qed.

Lemma derive_pt_pow :
  forall (n:nat) (x:R),
    derive_pt (fun y:R => y ^ n) x (derivable_pt_pow n x) = INR n * x ^ pred n.
Proof.
  intros; apply derive_pt_eq_0.
  apply derivable_pt_lim_pow.
Qed.

Lemma pr_nu :
  forall f (x:R) (pr1 pr2:derivable_pt f x),
    derive_pt f x pr1 = derive_pt f x pr2.
Proof.
  intros f x (x0,H0) (x1,H1).
  apply (uniqueness_limite f x x0 x1 H0 H1).
Qed.


(************************************************************)
(** *           Local extremum's condition                  *)
(************************************************************)

Lemma Rabs_prop : forall (x:R) (P : R -> Prop), (R0 <= x /\ P x) \/ ( x < R0 /\ P (-x)) -> P (Rabs x).
Proof.
intros x p [ [ hx hp ] | [ hx hp ] ].
rewrite Rabs_right. assumption. assumption.
rewrite Rabs_left. assumption. assumption.
Qed.

Lemma Rabs_prop_inv : forall (x:R) (P : R -> Prop), P (Rabs x) -> (R0 <= x /\ P x) \/ ( x < R0 /\ P (-x)).
Proof.
  intros x p h.
  unfold Rabs in h.
  destruct (Rcase_abs x) as [ hneg | hpos ].
  { right. split. exact hneg. exact h. }
  { left. split. exact hpos. exact h. }
Qed.

Lemma half_pos : forall x, R0 < x -> R0 < x / R2.
Proof.
  intros x hx.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  { exact hx. }
  {
    apply Rinv_0_lt_compat.
    exact Rlt_0_2.
  }
Qed.

Lemma half_lt : forall x, R0 < x -> x / R2 < x.
Proof.
  intros x hx.
  pattern x at 2;rewrite <- Rmult_1_r.
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  { exact hx. }
  {
    apply Rmult_lt_reg_l with R2.
    { exact Rlt_0_2. }
    {
      rewrite Rinv_r.
      2:exact Neq_2_0.
      rewrite double.
      pattern R1 at 1;rewrite <- Rplus_0_r.
      apply Rplus_lt_compat_l.
      exact Rlt_0_1.
    }
  }
Qed.

Lemma two_parts_pos : forall l, R0 < l -> exists la, exists lb, R0 < la /\ R0 < lb /\ la + lb = l.
Proof.
  intros l h.
  exists (l/R2).
  exists (l/R2).
  repeat (try split).
  { apply half_pos. exact h. }
  { apply half_pos. exact h. }
  {
    unfold Rdiv.
    rewrite <- Rmult_plus_distr_r.
    rewrite <- double.
    rewrite Rmult_comm.
    rewrite <- Rmult_assoc.
    rewrite Rinv_l.
    2:{ change (IZR 2) with R2. exact Neq_2_0. }
    rewrite Rmult_1_l.
    reflexivity.
  }
Qed.

Lemma two_parts_neg : forall l, l < R0 -> exists la, exists lb, la < R0 /\ lb < R0 /\ la + lb = l.
Proof.
  intros l h.
  apply Ropp_lt_contravar in h.
  rewrite Ropp_0 in h.
  apply two_parts_pos in h.
  destruct h as [ la [ lb [ hla [ hlb heq ] ] ] ].
  exists (-la).
  exists (-lb).
  repeat (try split).
  apply Ropp_lt_cancel. rewrite Ropp_0, Ropp_involutive. exact hla.
  apply Ropp_lt_cancel. rewrite Ropp_0, Ropp_involutive. exact hlb.
  rewrite <- Ropp_plus_distr.
  rewrite <- Ropp_involutive with l.
  apply Ropp_eq_compat.
  exact heq.
Qed.

Lemma two_parts : forall l, exists la, exists lb, la < R0 /\ R0 < lb /\ la + lb = l.
Proof.
  intro l.
  destruct (Rtotal_order l R0) as [ ho | [ ho | ho ] ].
  3:{
    exists (- R1). exists (R1+l).
    repeat (try split).
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar. exact Rlt_0_1.
    rewrite <- Rplus_0_l with R0.
    apply Rplus_lt_compat.
    exact Rlt_0_1.
    exact ho.
    rewrite <- Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l.
    reflexivity.
  }
  2:{
    subst l.
    exists (-R1).
    exists R1.
    repeat (try split).
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar. exact Rlt_0_1.
    exact Rlt_0_1.
    rewrite Rplus_opp_l.
    reflexivity.
  }
  {
    exists (l-R1).
    exists R1.
    repeat (try split).
    unfold Rminus.
    rewrite <- Rplus_0_r with R0.
    apply Rplus_lt_compat.
    exact ho.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact Rlt_0_1.
    exact Rlt_0_1.
    unfold Rminus.
    rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
    reflexivity.
  }
Qed.

Lemma lem : forall x, (forall e, R0 < e -> - e < x < e) -> x = R0.
Proof.
  intros x h.
  destruct (Rtotal_order x R0) as [ ho | [ ho | ho ] ].
  2:exact ho.
  2:{
    exfalso.
    specialize (h (x / R2)).
    assert ( ho' : R0 < x / R2).
    { apply half_pos. exact ho. }
    specialize (h ho').
    destruct h as [ hl hr ].
    eapply Rlt_irrefl.
    eapply Rlt_trans.
    apply hr.
    apply half_lt.
    exact ho.
  }
  {
    exfalso.
    specialize (h (-(x/R2))).
    assert ( ho' : R0 < -(x / R2) ).
    {
      unfold Rdiv.
      rewrite Ropp_mult_distr_l.
      apply half_pos.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact ho.
    }
    specialize (h ho').
    destruct h as [ hl hr ].
    rewrite Ropp_involutive in hl.
    exfalso.
    eapply Rlt_irrefl.
    eapply Rlt_trans.
    apply hl.
    pattern x at 1;rewrite (double_var x).
    change (IZR 2) with R2.
    eapply Rplus_lt_reg_r.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    apply Ropp_lt_cancel.
    unfold Rdiv.
    rewrite Ropp_0, Ropp_mult_distr_l.
    apply half_pos.
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact ho.
 }
Qed.

Theorem deriv_maximum :
  forall f (a b c:R) (pr:derivable_pt f c),
    a < c ->
    c < b ->
    (forall x:R, a < x -> x < b -> f x <= f c) -> derive_pt f c pr = R0.
Proof.

  intros f a b c pr hac hcb h.

  generalize derivable_derive; intro hex.
  specialize (hex f c pr).
  destruct hex as [ l hleq ].

  generalize derive_pt_eq_1 ; intro hlim.
  specialize (hlim f c l pr).
  specialize (hlim hleq).

  rewrite hleq.

  destruct (Rtotal_order R0 l) as [ ho | [ ho | ho ] ].
  {

    destruct (two_parts_pos l) as [ la [ lb [ hla [ hlb hlab ] ] ] ].
    exact ho.

    unfold derivable_pt_lim in hlim.
    specialize (hlim _ hla).
    destruct hlim as [ delta hlim ].

    assert (hk : exists k, k <> R0 /\ Rabs k < delta /\ a < c + k /\ c + k < b /\ R0 < k).
    {

      clear - hcb hac.

      set (exp := Rmin (delta / R2) ((b - c) / R2)).
      exists exp.

      assert (hminpos : R0 < exp).
      {
        unfold exp.
        apply Rmin_pos.
        {
          apply half_pos.
          apply cond_pos.
        }
        {
          apply half_pos.
          unfold Rminus.
          rewrite <- Rplus_opp_r with c.
          apply Rplus_lt_compat_r.
          exact hcb.
        }
      }

      repeat (try split).
      {
        apply Rlt_not_eq'.
        exact hminpos.
      }
      {
        rewrite Rabs_right.
        2:{
          left.
          exact hminpos.
        }
        {
          apply Rle_lt_trans with (delta/R2).
          {
            unfold exp.
            apply Rmin_l.
          }
          {
            apply half_lt.
            apply cond_pos.
          }
        }
      }
      {
        pattern a;rewrite <- Rplus_0_r.
        apply Rplus_lt_compat.
        { exact hac. }
        { exact hminpos. }
      }
      {
        rewrite Rplus_comm.
        apply Rplus_lt_reg_r with (-c).
        rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
        apply Rmult_lt_reg_r with (/R2).
        {
          apply Rinv_0_lt_compat.
          exact Rlt_0_2.
        }
        {
          unfold Rdiv, Rminus.
          eapply Rlt_le_trans.
          2:{ apply Rmin_r. }
          {
            apply half_lt.
            apply hminpos.
          }
        }
      }
      { exact hminpos. }
    }
    destruct hk as [ k [ hkneq [ hkd [ hka [ hkb hkpos ] ] ] ] ].

    specialize (hlim _ hkneq hkd).

    assert ( diff_neg : (f (c + k) - f c) / k <= R0).
    {
      clear - h hka hkb hkpos.
      unfold Rdiv.
      apply Ropp_le_cancel.
      rewrite Ropp_0.
      rewrite Ropp_mult_distr_l.
      apply Rmult_le_pos.
      {
        apply Ropp_le_cancel.
        rewrite Ropp_involutive, Ropp_0.
        eapply Rplus_le_reg_r.
        unfold Rminus.
        rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
        apply h.
        { exact hka. }
        { exact hkb. }
      }
      {
        left.
        apply Rinv_0_lt_compat.
        exact hkpos.
      }
    }

    unfold Rminus in hlim.

    apply Rabs_prop_inv in hlim.
    destruct hlim as [ [hpos hlim ] | [hneg hlim] ].
    {
      exfalso.
      clear - diff_neg hpos ho.
      eapply Rlt_irrefl.
      eapply Rle_lt_trans.
      apply diff_neg.
      clear diff_neg.
      apply Rplus_lt_reg_r with (-l).
      rewrite Rplus_0_l.
      eapply Rlt_le_trans.
      2:apply hpos.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact ho.
    }
    {
      exfalso.
      clear - diff_neg hlim hlab hlb.
      eapply Rlt_irrefl.
      eapply Rlt_le_trans.
      apply hlim.
      clear hlim.
      apply Ropp_le_cancel.
      rewrite Ropp_involutive.
      apply Rplus_le_reg_r with l.
      rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
      eapply Rle_trans.
      apply diff_neg.
      rewrite <- hlab.
      rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
      left.
      exact hlb.
    }
  }
  {
    symmetry.
    exact ho.
  }
  {
    unfold derivable_pt_lim in hlim.

    destruct (two_parts_pos (-l)) as [ la [ lb [ hla [ hlb hlab ]]]].
    { rewrite <- Ropp_0. apply Ropp_lt_contravar. exact ho. }

    specialize (hlim _ hla).
    destruct hlim as [ delta hlim ].

    set (exp := (Rmax (- (delta / R2)) ((a - c) / R2))).
    specialize (hlim exp).
    assert (expneg : exp < R0).
    {
      unfold exp.
      apply Rmax_neg.
      {
        rewrite <- Ropp_0.
        apply Ropp_lt_contravar.
        apply half_pos.
        apply cond_pos.
      }
      {
        apply Ropp_lt_cancel.
        rewrite Ropp_0.
        unfold Rdiv.
        rewrite Ropp_mult_distr_l.
        apply half_pos.
        apply Ropp_lt_cancel.
        rewrite Ropp_0.
        rewrite Ropp_involutive.
        apply Rplus_lt_reg_r with c.
        rewrite Rplus_comm.
        rewrite Rplus_minus.
        rewrite Rplus_0_l.
        exact hac.
      }
    }
    assert (expneq : exp <> R0).
    {
      apply Rlt_not_eq.
      exact expneg.
    }

    specialize (hlim expneq).

    assert (expinf : Rabs exp < delta).
    {
      rewrite Rabs_left.
      unfold exp.
      apply Ropp_lt_cancel.
      rewrite Ropp_involutive.
      eapply Rlt_le_trans.
      2:apply Rmax_l.
      apply Ropp_lt_contravar.
      apply half_lt.
      apply cond_pos.
      exact expneg.
    }

    specialize (hlim expinf).

    assert (hac_exp : a < c + exp).
    {
      unfold exp.
      apply Rplus_lt_reg_l with (-c).
      rewrite <- Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_comm, Rplus_0_l.
      eapply Rlt_le_trans.
      2:apply Rmax_r.
      apply Ropp_lt_cancel.
      unfold Rdiv.
      rewrite Ropp_mult_distr_l.
      apply half_lt.
      rewrite Ropp_plus_distr, Ropp_involutive.
      apply Rplus_lt_reg_l with a.
      rewrite <- Rplus_assoc, Rplus_opp_r, Rplus_0_l, Rplus_0_r.
      exact hac.
    }

    assert (hexp_cb : c + exp < b).
    {
      unfold exp.
      apply Rplus_lt_reg_l with (-c).
      rewrite <- Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_l.
      rewrite Rplus_comm.
      apply Rlt_trans with R0.
      apply Rmax_neg.
      { rewrite <- Ropp_0. apply Ropp_lt_contravar. apply half_pos. apply cond_pos. }
      { apply Ropp_lt_cancel. rewrite Ropp_0. unfold Rdiv. rewrite Ropp_mult_distr_l. apply half_pos.
        unfold Rminus. rewrite Ropp_plus_distr. rewrite Ropp_involutive. apply Rplus_lt_reg_l with a.
        rewrite Rplus_0_r, <- Rplus_assoc, Rplus_opp_r, Rplus_0_l.
        exact hac.
      }
      { apply Rplus_lt_reg_r with c. rewrite Rplus_assoc, Rplus_0_l, Rplus_opp_l, Rplus_0_r.
        exact hcb.
      }
    }

    apply Rabs_prop_inv in hlim.
    destruct hlim as [ [ hpos hlim ] | [ hneg hlim ] ].
    {
      exfalso.
      eapply Rlt_irrefl.
      eapply Rlt_le_trans.
      apply hlim.
      clear hpos hlim.
      unfold Rminus.
      rewrite <- hlab.
      rewrite (Rplus_comm la).
      pattern la at 1;rewrite <- Rplus_0_l.
      rewrite <- Rplus_assoc.
      apply Rplus_le_compat_r.
      apply Rle_trans with lb.
      left. exact hlb.
      pattern lb at 1;rewrite <- Rplus_0_l.
      apply Rplus_le_compat_r.
      apply Ropp_le_cancel.
      apply Ropp_le_cancel.
      repeat rewrite Ropp_0.
      unfold Rdiv.
      rewrite Ropp_mult_distr_l.
      rewrite Ropp_mult_distr_r.
      apply Rmult_le_pos.
      2:{
        rewrite Ropp_inv_permute.
        2:exact expneq.
        left. apply Rinv_0_lt_compat.
        rewrite <- Ropp_0.
        apply Ropp_lt_contravar.
        exact expneg.
      }
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      apply Rplus_le_reg_r with (f c).
      rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
      apply h.
      { exact hac_exp. }
      { exact hexp_cb. }
    }
    {
      exfalso.
      eapply Rlt_irrefl.
      eapply Rlt_le_trans.
      apply hneg.
      clear hneg hlim.
      unfold Rminus, Rdiv.
      apply Rplus_le_reg_r with l.
      rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
      apply Rle_trans with R0.
      { left. exact ho. }
      {
        apply Ropp_le_cancel.
        apply Ropp_le_cancel.
        repeat rewrite Ropp_0.
        rewrite Ropp_mult_distr_l.
        rewrite Ropp_mult_distr_r.
        apply Rmult_le_pos.
        2:{
          rewrite Ropp_inv_permute.
          2:exact expneq.
          left.
          apply Rinv_0_lt_compat.
          rewrite <- Ropp_0.
          apply Ropp_lt_contravar.
          exact expneg.
        }
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        apply Rplus_le_reg_r with (f c).
        rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
        apply h.
        { exact hac_exp. }
        { exact hexp_cb. }
      }
    }
  }
Qed.

Theorem deriv_minimum :
  forall f (a b c:R) (pr:derivable_pt f c),
    a < c ->
    c < b ->
    (forall x:R, a < x -> x < b -> f c <= f x) -> derive_pt f c pr = R0.
Proof.
  intros.
  rewrite <- (Ropp_involutive (derive_pt f c pr)).
  apply Ropp_eq_0_compat.
  rewrite <- (derive_pt_opp f c pr).
  cut (forall x:R, a < x -> x < b -> (- f)%F x <= (- f)%F c).
  intro.
  apply (deriv_maximum (- f)%F a b c (derivable_pt_opp _ _ pr) H H0 H2).
  intros; unfold opp_fct; apply Ropp_le_contravar.
  apply (H1 x H2 H3).
Qed.

Theorem deriv_constant2 :
  forall f (a b c:R) (pr:derivable_pt f c),
    a < c ->
    c < b -> (forall x:R, a < x -> x < b -> f x = f c) -> derive_pt f c pr = R0.
Proof.
  intros.
  eapply deriv_maximum with a b; try assumption.
  intros; right; apply (H1 x H2 H3).
Qed.

(**********)
Lemma nonneg_derivative_0 :
  forall f (pr:derivable f),
    increasing f -> forall x:R, R0 <= derive_pt f x (pr x).
Proof.
  intros; unfold increasing in H.
  assert (H0 := derivable_derive f x (pr x)).
  elim H0; intros l H1.
  rewrite H1; case (Rtotal_order R0 l); intro.
  left; assumption.
  elim H2; intro.
  right; assumption.
  assert (H4 := derive_pt_eq_1 f x l (pr x) H1).
  cut (R0 < - (l / R2)).
  intro; elim (H4 (- (l / R2)) H5); intros delta H6.
  cut (delta / R2 <> R0 /\ R0 < delta / R2 /\ Rabs (delta / R2) < delta).
  intro; decompose [and] H7; intros; generalize (H6 (delta / R2) H8 H11);
    cut (R0 <= (f (x + delta / R2) - f x) / (delta / R2)).
  intro; cut (R0 <= (f (x + delta / R2) - f x) / (delta / R2) - l).
  intro; unfold Rabs;
    case (Rcase_abs ((f (x + delta / R2) - f x) / (delta / R2) - l)) as [Hlt|Hge].
  elim
      (Rlt_irrefl R0
        (Rle_lt_trans R0 ((f (x + delta / R2) - f x) / (delta / R2) - l) R0 H12 Hlt)).
  intros;
    generalize
      (Rplus_lt_compat_r l ((f (x + delta / R2) - f x) / (delta / R2) - l)
        (- (l / R2)) H13); unfold Rminus;
      replace (- (l / R2) + l) with (l / R2).
  rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r; intro;
    generalize
      (Rle_lt_trans R0 ((f (x + delta / R2) - f x) / (delta / R2)) (l / R2) H9 H14);
      intro; cut (l / R2 < R0).
  intro; elim (Rlt_irrefl R0 (Rlt_trans R0 (l / R2) R0 H15 H16)).

  rewrite <- Ropp_0 in H5.
  apply Ropp_lt_cancel in H5. assumption.
  pattern l at 3; rewrite double_var.
{
change (IZR 2) with R2.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
}
  unfold Rminus; apply Rplus_le_le_0_compat.
  unfold Rdiv; apply Rmult_le_pos.
  cut (x <= x + delta * / R2).
  intro; generalize (H x (x + delta * / R2) H12); intro;
    generalize (Rplus_le_compat_l (- f x) (f x) (f (x + delta * / R2)) H13);
      rewrite Rplus_opp_l; rewrite Rplus_comm; intro; assumption.
  pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
    left; assumption.
  left; apply Rinv_0_lt_compat; assumption.
  left; rewrite <- Ropp_0; apply Ropp_lt_contravar; assumption.
  unfold Rdiv; apply Rmult_le_pos.
  cut (x <= x + delta * / R2).
  intro; generalize (H x (x + delta * / R2) H9); intro;
    generalize (Rplus_le_compat_l (- f x) (f x) (f (x + delta * / R2)) H12);
      rewrite Rplus_opp_l; rewrite Rplus_comm; intro; assumption.
  pattern x at 1; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
    left; assumption.
  left; apply Rinv_0_lt_compat; assumption.
  split.
  unfold Rdiv; apply prod_neq_R0.
  generalize (cond_pos delta); intro; red; intro H9; rewrite H9 in H7;
    elim (Rlt_irrefl R0 H7).
  apply Rinv_neq_0_compat; exact Neq_2_0.
  split.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply (cond_pos delta) | apply Rinv_0_lt_compat; exact Rlt_0_2 ].
  replace (Rabs (delta / R2)) with (delta / R2).
  unfold Rdiv; apply Rmult_lt_reg_l with R2.
  exact Rlt_0_2.
  rewrite (Rmult_comm R2).
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | exact Neq_2_0 ].
  rewrite Rmult_1_r.
  rewrite double.
  pattern (pos delta) at 1; rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l; apply (cond_pos delta).
  symmetry ; apply Rabs_right.
  left; change (R0 < delta / R2); unfold Rdiv;
    apply Rmult_lt_0_compat;
      [ apply (cond_pos delta) | apply Rinv_0_lt_compat; exact Rlt_0_2 ].
  unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse;
    apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_l with l.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rplus_0_r; assumption.
  apply Rinv_0_lt_compat; exact Rlt_0_2.
Qed.
