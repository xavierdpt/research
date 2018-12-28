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
Require Import XSeqSeries.
Require Import XRtrigo1.
Require Import XR_sqrt.
Local Open Scope XR_scope.

(** * Distance *)

Definition dist_euc (x0 y0 x1 y1:R) : R :=
  sqrt (Rsqr (x0 - x1) + Rsqr (y0 - y1)).

Lemma distance_refl : forall x0 y0:R, dist_euc x0 y0 x0 y0 = R0.
Proof.
  intros x0 y0; unfold dist_euc; apply Rsqr_inj;
    [ apply sqrt_positivity; apply Rplus_le_le_0_compat;
      [ apply Rle_0_sqr | apply Rle_0_sqr ]
      | right; reflexivity
      | rewrite Rsqr_0; rewrite Rsqr_sqrt;
        [ unfold Rsqr; idtac
          | apply Rplus_le_le_0_compat; [ apply Rle_0_sqr | apply Rle_0_sqr ] ] ].
unfold Rminus.
repeat rewrite Rplus_opp_r.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
reflexivity.
Qed.

Lemma distance_symm :
  forall x0 y0 x1 y1:R, dist_euc x0 y0 x1 y1 = dist_euc x1 y1 x0 y0.
Proof.
  intros x0 y0 x1 y1; unfold dist_euc; apply Rsqr_inj;
    [ apply sqrt_positivity; apply Rplus_le_le_0_compat
      | apply sqrt_positivity; apply Rplus_le_le_0_compat
      | repeat rewrite Rsqr_sqrt;
        [ unfold Rsqr; idtac
          | apply Rplus_le_le_0_compat
          | apply Rplus_le_le_0_compat ] ]; try apply Rle_0_sqr.
fold (Rsqr (x0-x1)).
fold (Rsqr (y0-y1)).
fold (Rsqr (x1-x0)).
fold (Rsqr (y1-y0)).
Search (Rsqr (_ - _)).
rewrite (Rsqr_neg_minus).
apply Rplus_eq_compat_l.
rewrite (Rsqr_neg_minus).
reflexivity.
Qed.

Lemma law_cosines :
  forall x0 y0 x1 y1 x2 y2 ac:R,
    let a := dist_euc x1 y1 x0 y0 in
      let b := dist_euc x2 y2 x0 y0 in
        let c := dist_euc x2 y2 x1 y1 in
          a * c * cos ac = (x0 - x1) * (x2 - x1) + (y0 - y1) * (y2 - y1) ->
          Rsqr b = Rsqr c + Rsqr a - R2 * (a * c * cos ac).
Proof.
  unfold dist_euc; intros; repeat rewrite Rsqr_sqrt;
    [ rewrite H; unfold Rsqr; idtac
      | apply Rplus_le_le_0_compat
      | apply Rplus_le_le_0_compat
      | apply Rplus_le_le_0_compat ]; try apply Rle_0_sqr.

rewrite double.
unfold Rminus.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite <- Ropp_mult_distr_r.
repeat rewrite Ropp_involutive.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
repeat rewrite <- Rplus_assoc.
repeat rewrite Ropp_plus_distr.
repeat rewrite Ropp_involutive.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
symmetry.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
symmetry.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
symmetry.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
rewrite Rmult_comm.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
rewrite Rmult_comm.
rewrite <- Rplus_0_r.
repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
rewrite (Rplus_comm _ (- (x1*x2))).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (- (x0*x1))).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (x1*x1)).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (- (y1*y2))).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (- (y0*y1))).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (y1*y1)).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (x1*x2)).
repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (- (x1*x1))).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (y1*y2)).
repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (- (y1*y1))).
repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
rewrite (Rplus_comm _ (x0*x1)).
repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
rewrite Rmult_comm. rewrite Rplus_opp_l.
reflexivity.
Qed.

Lemma triangle :
  forall x0 y0 x1 y1 x2 y2:R,
    dist_euc x0 y0 x1 y1 <= dist_euc x0 y0 x2 y2 + dist_euc x2 y2 x1 y1.
Proof.
  intros; unfold dist_euc; apply Rsqr_incr_0;
    [ rewrite Rsqr_plus; repeat rewrite Rsqr_sqrt;
      [ replace (Rsqr (x0 - x1)) with
        (Rsqr (x0 - x2) + Rsqr (x2 - x1) + R2 * (x0 - x2) * (x2 - x1));
        [ replace (Rsqr (y0 - y1)) with
          (Rsqr (y0 - y2) + Rsqr (y2 - y1) + R2 * (y0 - y2) * (y2 - y1));
          [ apply Rplus_le_reg_l with
            (- Rsqr (x0 - x2) - Rsqr (x2 - x1) - Rsqr (y0 - y2) -
              Rsqr (y2 - y1));
            replace
            (- Rsqr (x0 - x2) - Rsqr (x2 - x1) - Rsqr (y0 - y2) -
              Rsqr (y2 - y1) +
              (Rsqr (x0 - x2) + Rsqr (x2 - x1) + R2 * (x0 - x2) * (x2 - x1) +
                (Rsqr (y0 - y2) + Rsqr (y2 - y1) + R2 * (y0 - y2) * (y2 - y1))))
            with (R2 * ((x0 - x2) * (x2 - x1) + (y0 - y2) * (y2 - y1)));
              [ replace
                (- Rsqr (x0 - x2) - Rsqr (x2 - x1) - Rsqr (y0 - y2) -
                  Rsqr (y2 - y1) +
                  (Rsqr (x0 - x2) + Rsqr (y0 - y2) +
                    (Rsqr (x2 - x1) + Rsqr (y2 - y1)) +
                    R2 * sqrt (Rsqr (x0 - x2) + Rsqr (y0 - y2)) *
                    sqrt (Rsqr (x2 - x1) + Rsqr (y2 - y1)))) with
                (R2 *
                  (sqrt (Rsqr (x0 - x2) + Rsqr (y0 - y2)) *
                    sqrt (Rsqr (x2 - x1) + Rsqr (y2 - y1))));
                [ (*apply Rmult_le_compat_l;
                  [ left; cut (0%nat <> 2%nat);
                    [ intros; generalize (lt_INR_0 2 (neq_O_lt 2 H));
                      intro H0; assumption
                      | discriminate ]
                    | apply sqrt_cauchy ] *) idtac
                  | idtac ]
                | idtac ]
            | idtac ]
          | idtac ]
        | apply Rplus_le_le_0_compat; apply Rle_0_sqr
        | apply Rplus_le_le_0_compat; apply Rle_0_sqr
        | apply Rplus_le_le_0_compat; apply Rle_0_sqr ]
      | apply sqrt_positivity; apply Rplus_le_le_0_compat; apply Rle_0_sqr
      | apply Rplus_le_le_0_compat; apply sqrt_positivity;
        apply Rplus_le_le_0_compat; apply Rle_0_sqr ].
{
  change (IZR 2) with R2.
  assert (sc:=sqrt_cauchy).
  specialize (sc (x0 - x2)).
  specialize (sc (y0 - y2)).
  specialize (sc (x2 - x1)).
  specialize (sc (y2 - y1)).
  pose (a := x0 - x2). fold a. fold a in sc.
  pose (b := y0 - y2). fold b. fold b in sc.
  pose (c := x2 - x1). fold c. fold c in sc.
  pose (d := y2 - y1). fold d. fold d in sc.
  unfold Rminus.
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (Rsqr a)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr c)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr b)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr d)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  repeat rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  left. exact Rlt_0_2.
  exact sc.
}
{
  symmetry.
  unfold Rminus.
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (Rsqr (x0 + - x2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr (x2 + - x1))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr (y0 + - y2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite Rplus_opp_l. rewrite Rplus_0_l.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  reflexivity.
}
{
  symmetry.
  unfold Rminus.
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (Rsqr (x0 + - x2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr (x2 + - x1))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr (y0 + - y2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (Rsqr (y2 + - y1))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  repeat rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_l.
  apply Rmult_eq_compat_l.
  reflexivity.
}
{
  rewrite double.
  unfold Rminus.
  unfold Rsqr.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite Ropp_involutive.
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (y1*y1)).
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite (Rplus_comm _ (-(y0*y1))).
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite (Rplus_comm _ (-(y1*y0))).
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite <- Rplus_0_l.
  rewrite (Rplus_comm _ (-(y0*y1))).
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  rewrite (Rmult_comm y0 y1).
  apply Rplus_eq_compat_r.
  rewrite (Rplus_comm _ (y0*y2)).
  repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (y2*y0)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (-(y2*y2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (-(y2*y2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (y2*y1)).
  repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite Rplus_opp_l. reflexivity.
}
{
  unfold Rsqr.
  unfold Rminus.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite Ropp_involutive.
  repeat rewrite double.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite Ropp_involutive.
  repeat rewrite <- Rplus_assoc.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Ropp_plus_distr.
  repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (x0*x2)).
  repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (x2*x0)).
  repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (-(x2*x2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (-(x2*x2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (x2*x1)).
  repeat rewrite <- Rplus_assoc. rewrite Rmult_comm. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite (Rplus_comm _ (x1*x2)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_l.
  rewrite Rplus_comm.
  rewrite Rmult_comm.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  reflexivity.
}
Qed.

(******************************************************************)
(** *                       Translation                           *)
(******************************************************************)

Definition xt (x tx:R) : R := x + tx.
Definition yt (y ty:R) : R := y + ty.

Lemma translation_0 : forall x y:R, xt x R0 = x /\ yt y R0 = y.
Proof.
  intros x y; split; [ unfold xt | unfold yt ].
  rewrite Rplus_0_r;reflexivity.
  rewrite Rplus_0_r;reflexivity.
Qed.

Lemma isometric_translation :
  forall x1 x2 y1 y2 tx ty:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xt x1 tx - xt x2 tx) + Rsqr (yt y1 ty - yt y2 ty).
Proof.
  intros; unfold Rsqr, xt, yt.
  unfold Rminus.
  repeat rewrite Ropp_plus_distr.
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ tx).
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (-tx)).
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ ty).
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (-ty)).
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  reflexivity.
Qed.

(******************************************************************)
(** *                         Rotation                            *)
(******************************************************************)

Definition xr (x y theta:R) : R := x * cos theta + y * sin theta.
Definition yr (x y theta:R) : R := - x * sin theta + y * cos theta.

Lemma rotation_0 : forall x y:R, xr x y R0 = x /\ yr x y R0 = y.
Proof.
  intros x y; unfold xr, yr; split; rewrite cos_0; rewrite sin_0.
  rewrite Rmult_0_r, Rmult_1_r, Rplus_0_r. reflexivity.
  rewrite Rmult_0_r, Rmult_1_r, Rplus_0_l. reflexivity.
Qed.

Lemma rotation_PI2 :
  forall x y:R, xr x y (PI / R2) = y /\ yr x y (PI / R2) = - x.
Proof.
  intros x y; unfold xr, yr; split; rewrite cos_PI2; rewrite sin_PI2.
  rewrite Rmult_0_r, Rmult_1_r, Rplus_0_l. reflexivity.
  rewrite Rmult_0_r, Rmult_1_r, Rplus_0_r. reflexivity.
Qed.

Lemma isometric_rotation_0 :
  forall x1 y1 x2 y2 theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xr x1 y1 theta - xr x2 y2 theta) +
    Rsqr (yr x1 y1 theta - yr x2 y2 theta).
Proof.
  intros; unfold xr, yr;
    replace
    (x1 * cos theta + y1 * sin theta - (x2 * cos theta + y2 * sin theta)) with
    (cos theta * (x1 - x2) + sin theta * (y1 - y2));
    [ replace
      (- x1 * sin theta + y1 * cos theta - (- x2 * sin theta + y2 * cos theta))
      with (cos theta * (y1 - y2) + sin theta * (x2 - x1));
        [ repeat rewrite Rsqr_plus; repeat rewrite Rsqr_mult; repeat rewrite cos2
          (*
          ring_simplify; replace (x2 - x1) with (- (x1 - x2));
          [ rewrite <- Rsqr_neg; ring | ring ] *)
          | idtac ]
      | idtac ].
{
  unfold Rminus.
  unfold Rsqr.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  change (IZR 2) with R2.
  unfold R2.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite Ropp_involutive.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite Ropp_involutive.
  set (st := sin theta).
  set (ct := cos theta).
  symmetry.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rplus_comm _ (-(x1*x2))).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (x2*x2)).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (y1*y1)).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (-(y2*y1))).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (-(y1*y2))).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite <- Rplus_0_r.
  rewrite (Rplus_comm _ (y2*y2)).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_comm _ (st*st*x1*x1)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (-(st*st*x2*x1))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ (-(st*st*x1*x2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ (st*st*x2*x2)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (-(st*st*y1*y1))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ (st*st*y2*y1)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (st*st*y1*y2)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (-(st*st*y2*y2))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ (-(ct*y1*st*x1))).
  repeat rewrite <- Rplus_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y1); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm st); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y1); repeat rewrite <- Rmult_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ (-(ct*x1*st*y1))).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_l, Rplus_0_l.
  rewrite (Rplus_comm _ (ct*y1*st*x2)).
  repeat rewrite <- Rplus_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y1); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm st); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y1); repeat rewrite <- Rmult_assoc.
  rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (ct*x2*st*y1)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (ct*y2*st*x1)).
  repeat rewrite <- Rplus_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y2); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm st); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y2); repeat rewrite <- Rmult_assoc.
  rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (ct*x1*st*y2)).
  repeat rewrite <- Rplus_assoc. rewrite Rplus_opp_r, Rplus_0_l.
  rewrite (Rplus_comm _ (-(ct*y2*st*x2))).
  repeat rewrite <- Rplus_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y2); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm st); repeat rewrite <- Rmult_assoc.
    repeat rewrite Rmult_assoc; rewrite (Rmult_comm y2); repeat rewrite <- Rmult_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  rewrite Rplus_opp_r.
  reflexivity.
}
{
  unfold Rminus.
  rewrite Ropp_plus_distr.
  repeat rewrite <- Ropp_mult_distr_l.
  rewrite Ropp_involutive.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  rewrite (Rmult_comm _ y1).
  rewrite (Rmult_comm _ y2).
  rewrite (Rmult_comm _ x2).
  rewrite (Rmult_comm _ x1).
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc; apply Rplus_eq_compat_r.
  repeat rewrite <- Rplus_assoc; rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc; rewrite Rplus_comm.
  repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  reflexivity.
}
{
  unfold Rminus.
  rewrite Ropp_plus_distr.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  rewrite (Rmult_comm _ y1).
  rewrite (Rmult_comm _ y2).
  rewrite (Rmult_comm _ x2).
  rewrite (Rmult_comm _ x1).
  repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l.
  repeat rewrite <- Rplus_assoc; apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
}
Qed.

Lemma isometric_rotation :
  forall x1 y1 x2 y2 theta:R,
    dist_euc x1 y1 x2 y2 =
    dist_euc (xr x1 y1 theta) (yr x1 y1 theta) (xr x2 y2 theta)
    (yr x2 y2 theta).
Proof.
  unfold dist_euc; intros; apply Rsqr_inj;
    [ apply sqrt_positivity; apply Rplus_le_le_0_compat
      | apply sqrt_positivity; apply Rplus_le_le_0_compat
      | repeat rewrite Rsqr_sqrt;
        [ apply isometric_rotation_0
          | apply Rplus_le_le_0_compat
          | apply Rplus_le_le_0_compat ] ]; apply Rle_0_sqr.
Qed.

(******************************************************************)
(** *                       Similarity                            *)
(******************************************************************)

Lemma isometric_rot_trans :
  forall x1 y1 x2 y2 tx ty theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xr (xt x1 tx) (yt y1 ty) theta - xr (xt x2 tx) (yt y2 ty) theta) +
    Rsqr (yr (xt x1 tx) (yt y1 ty) theta - yr (xt x2 tx) (yt y2 ty) theta).
Proof.
  intros; rewrite <- isometric_rotation_0; apply isometric_translation.
Qed.

Lemma isometric_trans_rot :
  forall x1 y1 x2 y2 tx ty theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xt (xr x1 y1 theta) tx - xt (xr x2 y2 theta) tx) +
    Rsqr (yt (yr x1 y1 theta) ty - yt (yr x2 y2 theta) ty).
Proof.
  intros; rewrite <- isometric_translation; apply isometric_rotation_0.
Qed.
