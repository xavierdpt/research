(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**********************************************************)
(** Complements for the reals.Integer and fractional part *)
(*                                                        *)
(**********************************************************)

Require Import Rbase.
Require Import Omega.
Local Open Scope R_scope.

(*********************************************************)
(** *    Fractional part                                 *)
(*********************************************************)

(**********)
Definition Int_part (r:R) : Z := (up r - 1)%Z.

(**********)
Definition frac_part (r:R) : R := r - IZR (Int_part r).

(* Sufficient conditions for a Z integer to be equal to (up r) *)
Lemma tech_up : forall (r:R) (z:Z),
  r <  IZR z -> IZR z <= r + 1 ->
  z = up r.
Proof.

  intros r z hrzl hrzr.

  (* IZR (up r) > r /\ IZR (up r) - r <= 1 *)
  (* equivalent to : r < IZR (up r) <= 1 + r *)
  (* archimed is the only axiom about up so far *)
  destruct (archimed r) as [ hrul hrur ].

 (* it's visually better when every comparison is in the same direction *)
  apply Rgt_lt in hrul.

  (* single_z_r_R1 : transfer equality on integers to equality over IZR
      r < IZR n <= r + 1 ->
      r < IZR m <= r + 1 ->
      n = m
  *)
  apply single_z_r_R1 with r.
  { exact hrzl. (* hypothesis *) }
  { exact hrzr. (* hypothesis *) }
  { exact hrul. (* from archimed on r *) }
  { (* some rewriting to adapt to the other part of archimed on r *)
    (* links the remaining prerequisite of single_z_r_R1 to the upper part of archimed on r *)
    apply Rplus_le_reg_r with (-r).
    rewrite (Rplus_comm r).
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    exact hrur.
  }
Qed.


Lemma up_tech : forall (r:R) (z:Z),
  IZR z <= r -> r < IZR (z + 1) ->
  (z + 1)%Z = up r.
Proof.
  intros r z hl hr.
  apply tech_up.
  exact hr.
  rewrite plus_IZR.
  apply Rplus_le_compat_r.
  exact hl.
Qed.

Lemma up_0_1 : up 0 = 1%Z.
Proof.
  symmetry.
  apply tech_up.
  apply Rlt_0_1.
  rewrite Rplus_0_l. right. reflexivity.
Qed.

Lemma fp_R0 : frac_part 0 = 0.
Proof.
  unfold frac_part.
  unfold Int_part.
  rewrite up_0_1.
  rewrite <- minus_IZR.
  simpl. reflexivity.
Qed.

(* Reformulation of archimed for base_fp *)
Lemma for_base_fp : forall r:R, IZR (up r) - r > 0 /\ IZR (up r) - r <= 1.
Proof.
  intro r.
  destruct (archimed r) as [ hl hr].
  split.
  { apply Rgt_minus. exact hl. }
  { exact hr. }
Qed.

Lemma base_fp : forall r:R,
  frac_part r >= 0 /\ frac_part r < 1.
Proof.
  intro r.

  destruct (for_base_fp r) as [ hl hr ].
  
  assert (a1 : r - IZR (up r) >= -1).
  {
    rewrite <- Ropp_minus_distr.
    apply Ropp_le_ge_contravar.
    exact hr.
  }

  assert (a2 : r - IZR (up r) < 0).
  {
    rewrite <- Ropp_0.
    rewrite <- Ropp_minus_distr.
    apply Ropp_gt_lt_contravar.
    exact hl.
  }

  unfold frac_part. unfold Int_part. split.
  (* these two parts could be improved further *)
  {
    rewrite <- Z_R_minus.
    simpl.
    unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite <- Rplus_assoc.
    fold (r - IZR (up r)).
    unfold IZR at 2.
    apply Rge_minus.
    exact a1.
  }
  {
    rewrite <- Z_R_minus.
    simpl.
    unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite <- Rplus_assoc.
    fold (r - IZR (up r)).
    rewrite Ropp_involutive.
    elim (Rplus_ne 1). intros a b. pattern 1 at 2.
    rewrite <- a. clear a b.
    rewrite (Rplus_comm (r - IZR (up r)) 1).
    apply Rplus_lt_compat_l.
    exact a2.
  }
Qed.

(* stopped here *)

Lemma base_Int_part :  forall r:R,
  IZR (Int_part r) <= r /\ IZR (Int_part r) - r > -1.
Proof.
  intro; unfold Int_part; elim (archimed r); intros.
  split; rewrite <- (Z_R_minus (up r) 1); simpl.
  apply Rminus_le.
  replace (IZR (up r) - 1 - r) with (IZR (up r) - r - 1) by ring.
  now apply Rle_minus.
  apply Rminus_gt.
  replace (IZR (up r) - 1 - r - -1) with (IZR (up r) - r) by ring.
  now apply Rgt_minus.
Qed.

Lemma Int_part_INR : forall n:nat,
  Int_part (INR n) = Z.of_nat n.
Proof.
  intros n; unfold Int_part.
  cut (up (INR n) = (Z.of_nat n + Z.of_nat 1)%Z).
  intros H'; rewrite H'; simpl; ring.
  symmetry; apply tech_up; auto.
  replace (Z.of_nat n + Z.of_nat 1)%Z with (Z.of_nat (S n)).
  repeat rewrite <- INR_IZR_INZ.
  apply lt_INR; auto.
  rewrite Z.add_comm; rewrite <- Znat.Nat2Z.inj_add; simpl; auto.
  rewrite plus_IZR; simpl; auto with real.
  repeat rewrite <- INR_IZR_INZ; auto with real.
Qed.

Lemma fp_nat : forall r:R,
  frac_part r = 0 ->
  exists c : Z, r = IZR c.
Proof.
  unfold frac_part; intros; split with (Int_part r);
    apply Rminus_diag_uniq; auto with zarith real.
Qed.

Lemma R0_fp_O : forall r:R,
  0 <> frac_part r ->
  0 <> r.
Proof.
  red; intros; rewrite <- H0 in H; generalize fp_R0; intro;
    auto with zarith real.
Qed.

Definition iip (r:R) :=  IZR (Int_part r).
Definition iup (r:R) := IZR (up r).

Lemma youpi1 : (forall a b c, a=c+b -> a-b=c)%Z.
Proof.
  intros a b c h.
  rewrite h. unfold Z.sub. rewrite <- Z.add_assoc. rewrite Z.add_opp_diag_r. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma Rminus_Int_part1 : forall r1 r2:R,
  frac_part r1 >= frac_part r2 ->
  Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z.
Proof.

  intros r1 r2 H.

  unfold Int_part at 1.
  apply youpi1.
  symmetry.
  apply up_tech.

  {
    unfold frac_part in H.
    unfold Z.sub.
    rewrite plus_IZR.
    apply Rge_le.
    unfold Rminus in *.
    apply Rplus_ge_reg_l with r2.
    rewrite (Rplus_comm r2).
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    rewrite opp_IZR.
    apply Rplus_ge_reg_l with (- IZR (Int_part r1)).
    rewrite (Rplus_comm _ r1).
    rewrite <- Rplus_assoc.
    rewrite (Rplus_comm _ r2).
    rewrite Rplus_assoc.
    rewrite <- (Rplus_assoc (- IZR (Int_part r1))).
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l.
    exact H.
  }
  {

    destruct (base_fp r1) as [ r1l r1r].
    destruct (base_fp r2) as [ r2l r2r].

    rewrite plus_IZR.
    unfold Z.sub.
    rewrite plus_IZR.
    rewrite opp_IZR.

    unfold Rminus.
    apply Rplus_lt_reg_l with ( - IZR (Int_part r1) ).
    rewrite <- Rplus_assoc.
    rewrite (Rplus_comm _ r1).
    fold (r1 - IZR (Int_part r1)).
    fold (frac_part r1).
    
    repeat (rewrite <- Rplus_assoc).
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l.
    
    apply Rplus_lt_reg_l with r2.
    repeat (rewrite <- Rplus_assoc).
    fold (r2 - IZR (Int_part r2)).
    fold (frac_part r2).

    rewrite (Rplus_comm r2).
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.

    apply Rge_le in H.
    apply Rge_le in r1l.
    apply Rge_le in r2l.

    destruct r1l as [lt1 | eq1 ] ; destruct r2l as [lt2 | eq2].
    {
      apply Rlt_trans with 1. exact r1r.
      pattern 1 at 1;rewrite <- Rplus_0_l with 1.
      apply Rplus_lt_compat_r. exact lt2.
    }
    {
      rewrite <- eq2 in *. clear eq2. rewrite Rplus_0_l. exact r1r.
    }
    {
      rewrite <- eq1 in *. clear eq1.
      apply Rlt_trans with (frac_part r2). exact lt2.
      apply Rlt_plus_1.
    }
    {
      rewrite <- eq1 in *. clear eq1.
      rewrite <- eq2 in *. clear eq2.
      rewrite Rplus_0_l. exact r1r.
    }
  }
Qed.


Lemma Rminus_Int_part2 : forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2 - 1)%Z.
Proof.

intros.

destruct (base_fp r1) as [H2 H3].
destruct (base_fp r2) as [H0 H1].

(* (z + 1)%Z = up r *)
unfold Rminus.
unfold Int_part.
apply youpi1.
fold (r1 - r2).
unfold Z.sub.
rewrite <- Z.add_assoc.
rewrite Z.add_opp_diag_l.
rewrite Z.add_0_r.
Search (  - ( _ + _))%Z.
rewrite Z.opp_add_distr.
rewrite Z.opp_involutive.
rewrite <- Z.add_assoc.
rewrite (Z.add_comm (-1))%Z.
rewrite <- Z.add_assoc.
rewrite Z.add_opp_diag_r.
rewrite Z.add_0_r.
fold (up r1 - up r2)%Z.

Search (_ = up _).
symmetry.
apply tech_up.

{

unfold Z.sub.
rewrite plus_IZR.
rewrite opp_IZR.

unfold frac_part in *.
unfold Int_part in *.
unfold Z.sub in *.
rewrite plus_IZR in *.
rewrite plus_IZR in *.
rewrite opp_IZR in *.
unfold Rminus in *.
rewrite Ropp_plus_distr in *.
Search (- - _).
rewrite Ropp_involutive in *.

apply Rge_le in H2.
apply Rge_le in H0.

apply Rplus_lt_reg_r with r2.
repeat (rewrite Rplus_assoc).
rewrite Rplus_opp_l.
rewrite Rplus_0_r.

apply Rplus_lt_reg_l with (- IZR (up r1)).

repeat (rewrite <- Rplus_assoc).
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite (Rplus_comm _ r1).
rewrite (Rplus_comm _ r2).

fold (iup r1) in *.
fold (iup r2) in *.

admit.
}
{
  unfold frac_part in *.
  unfold Int_part in *.
  rewrite minus_IZR in *.
  rewrite minus_IZR in *.
  pose (a1 := IZR (up r1)).
  pose (a2 := IZR (up r2)).
  fold a1 in H, H2, H3, H0, H1.
  fold a2 in H, H2, H3, H0, H1.
  fold a1.
  fold a2.
  unfold Rminus in *.

  apply Rge_le in H2.
  apply Rge_le in H0.

  rewrite Ropp_plus_distr in H.
  rewrite Ropp_plus_distr in H.
  rewrite Ropp_involutive in H.

  rewrite Ropp_plus_distr in H2.
  rewrite Ropp_involutive in H2.

  rewrite Ropp_plus_distr in H3.
  rewrite Ropp_involutive in H3.

  rewrite Ropp_plus_distr in H0.
  rewrite Ropp_involutive in H0.

  rewrite Ropp_plus_distr in H1.
  rewrite Ropp_involutive in H1.

    
}

apply Rge_le in H0. rename H0 into H4.
apply Ropp_le_ge_contravar in H4. rename H4 into H0.
rewrite Ropp_0 in H0.
apply Rge_le in H0. rename H0 into H4.
apply Rge_le in H2. rename H2 into H0.
apply Ropp_lt_gt_contravar in H1. rename H1 into H2.
unfold Rgt in H2.

destruct (sum_inequa_Rle_lt 0 (frac_part r1) 1 (-1) (- frac_part r2) 0 H0 H3 H2 H4) as [H5 H6].

rewrite Rplus_0_l in H5.
clear H6.

apply Rlt_minus in H. rename H into H1.

fold (frac_part r1 - frac_part r2) in H5.

clear H3 H4 H0 H2.

unfold frac_part in H5, H1.
unfold Rminus in H5, H1.

rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2))) in H5.
rewrite (Ropp_involutive (IZR (Int_part r2))) in H5.
rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2))) in H5.
rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2))) in H5.
rewrite (Rplus_comm (- IZR (Int_part r1)) (- r2)) in H5.
rewrite (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2))) in H5.
rewrite <- (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2))) in H5.
rewrite (Rplus_comm (- IZR (Int_part r1)) (IZR (Int_part r2))) in H5.
fold (r1 - r2) in H5.
fold (IZR (Int_part r2) - IZR (Int_part r1)) in H5.

apply (Rplus_lt_compat_l (IZR (Int_part r1) - IZR (Int_part r2))) in H5.
rename H5 into H.

rewrite (Rplus_comm (r1 - r2) (IZR (Int_part r2) - IZR (Int_part r1))) in H.
rewrite <- (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2)) (IZR (Int_part r2) - IZR (Int_part r1)) (r1 - r2)) in H.
unfold Rminus in H.
fold (r1 - r2) in H.
rewrite (Rplus_assoc (IZR (Int_part r1)) (- IZR (Int_part r2)) (IZR (Int_part r2) + - IZR (Int_part r1))) in H.
rewrite <- (Rplus_assoc (- IZR (Int_part r2)) (IZR (Int_part r2)) (- IZR (Int_part r1))) in H.
rewrite (Rplus_opp_l (IZR (Int_part r2))) in H.
rewrite Rplus_0_l in H.
rewrite (Rplus_opp_r (IZR (Int_part r1))) in H.
rewrite Rplus_0_l in H.

fold (IZR (Int_part r1) - IZR (Int_part r2)) in H.
fold (IZR (Int_part r1) - IZR (Int_part r2) - 1) in H.

rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2))) in H1.
rewrite (Ropp_involutive (IZR (Int_part r2))) in H1.
rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2))) in H1.
rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2))) in H1.
rewrite (Rplus_comm (- IZR (Int_part r1)) (- r2)) in H1.
rewrite (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2))) in H1.
rewrite <- (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2))) in H1.
rewrite (Rplus_comm (- IZR (Int_part r1)) (IZR (Int_part r2))) in H1.

fold (r1 - r2) in H1.
fold (IZR (Int_part r2) - IZR (Int_part r1)) in H1.

apply (Rplus_lt_compat_l (IZR (Int_part r1) - IZR (Int_part r2))) in H1.
rename H1 into H0.

rewrite (Rplus_comm (r1 - r2) (IZR (Int_part r2) - IZR (Int_part r1))) in H0.
rewrite <- (Rplus_assoc (IZR (Int_part r1) - IZR (Int_part r2)) (IZR (Int_part r2) - IZR (Int_part r1)) (r1 - r2)) in H0.
rewrite <- (Ropp_minus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H0.
rewrite (Rplus_opp_r (IZR (Int_part r1) - IZR (Int_part r2))) in H0.
rewrite Rplus_0_r in H0.

rewrite <- (Rplus_opp_l 1) in H0.
unfold IZR at 1 in H0.
unfold IPR in H0.
unfold Rminus in H0.

fold (IZR (Int_part r1) - IZR (Int_part r2)) in H0.
rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H0.
rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H.
auto with zarith real.

change (_ + -1) with (IZR (Int_part r1 - Int_part r2) - 1) in H.

rewrite (Z_R_minus (Int_part r1 - Int_part r2) 1) in H.

apply Rlt_le in H. rename H into H1.
rewrite Rplus_opp_l in H0. rewrite Rplus_0_l in H0.
fold (r1  - r2) in H0.

assert (eq:(Int_part r1 - Int_part r2 = Int_part r1 - Int_part r2-1+1)%Z).
unfold Z.sub.
rewrite <- Z.add_assoc.
rewrite Z.add_opp_diag_l.
rewrite Z.add_0_r.
reflexivity.
rewrite eq in H0.
generalize (up_tech (r1 - r2) (Int_part r1 - Int_part r2 - 1) H1 H0).

intros H.

clear H0 H1.

unfold Int_part at 1.


omega.
Qed.

(**********)
Lemma Rminus_fp1 :
  forall r1 r2:R,
    frac_part r1 >= frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2.
Proof.
  intros; unfold frac_part; generalize (Rminus_Int_part1 r1 r2 H);
    intro; rewrite H0; rewrite <- (Z_R_minus (Int_part r1) (Int_part r2));
      unfold Rminus;
        rewrite (Ropp_plus_distr (IZR (Int_part r1)) (- IZR (Int_part r2)));
          rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2)));
            rewrite (Ropp_involutive (IZR (Int_part r2)));
              rewrite (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)));
                rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)));
                  rewrite <- (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2)));
                    rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)));
                      rewrite (Rplus_comm (- r2) (- IZR (Int_part r1)));
                        auto with zarith real.
Qed.

(**********)
Lemma Rminus_fp2 :
  forall r1 r2:R,
    frac_part r1 < frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2 + 1.
Proof.
  intros; unfold frac_part; generalize (Rminus_Int_part2 r1 r2 H);
    intro; rewrite H0; rewrite <- (Z_R_minus (Int_part r1 - Int_part r2) 1);
      rewrite <- (Z_R_minus (Int_part r1) (Int_part r2));
        unfold Rminus;
          rewrite
            (Ropp_plus_distr (IZR (Int_part r1) + - IZR (Int_part r2)) (- IZR 1))
            ; rewrite (Ropp_plus_distr r2 (- IZR (Int_part r2)));
              rewrite (Ropp_involutive (IZR 1));
                rewrite (Ropp_involutive (IZR (Int_part r2)));
                  rewrite (Ropp_plus_distr (IZR (Int_part r1)));
                    rewrite (Ropp_involutive (IZR (Int_part r2))); simpl;
                      rewrite <-
                        (Rplus_assoc (r1 + - r2) (- IZR (Int_part r1) + IZR (Int_part r2)) 1)
                        ; rewrite (Rplus_assoc r1 (- r2) (- IZR (Int_part r1) + IZR (Int_part r2)));
                          rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (- r2 + IZR (Int_part r2)));
                            rewrite <- (Rplus_assoc (- r2) (- IZR (Int_part r1)) (IZR (Int_part r2)));
                              rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- r2) (IZR (Int_part r2)));
                                rewrite (Rplus_comm (- r2) (- IZR (Int_part r1)));
                                  auto with zarith real.
Qed.

(**********)
Lemma plus_Int_part1 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 >= 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2 + 1)%Z.
Proof.
  intros; generalize (Rge_le (frac_part r1 + frac_part r2) 1 H); intro; clear H;
    elim (base_fp r1); elim (base_fp r2); intros; clear H H2;
      generalize (Rplus_lt_compat_l (frac_part r2) (frac_part r1) 1 H3);
        intro; clear H3; generalize (Rplus_lt_compat_l 1 (frac_part r2) 1 H1);
          intro; clear H1; rewrite (Rplus_comm 1 (frac_part r2)) in H2;
            generalize
              (Rlt_trans (frac_part r2 + frac_part r1) (frac_part r2 + 1) 2 H H2);
              intro; clear H H2; rewrite (Rplus_comm (frac_part r2) (frac_part r1)) in H1;
                unfold frac_part in H0, H1; unfold Rminus in H0, H1;
                  rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                    in H1; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H1;
                      rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2)
                        in H1;
                        rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H1;
                          rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                            in H1;
                            rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
                              rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                                in H0; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H0;
                                  rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2)
                                    in H0;
                                    rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H0;
                                      rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                                        in H0;
                                        rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H0;
                                          generalize
                                            (Rplus_le_compat_l (IZR (Int_part r1) + IZR (Int_part r2)) 1
                                              (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) H0);
                                            intro; clear H0;
                                              generalize
                                                (Rplus_lt_compat_l (IZR (Int_part r1) + IZR (Int_part r2))
                                                  (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) 2 H1);
                                                intro; clear H1;
                                                  rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                    in H;
                                                    rewrite <-
                                                      (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                        (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                      in H; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H;
                                                        elim (Rplus_ne (r1 + r2)); intros a b; rewrite b in H;
                                                          clear a b;
                                                            rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                              in H0;
                                                              rewrite <-
                                                                (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                                  (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                                in H0; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H0;
                                                                  elim (Rplus_ne (r1 + r2)); intros a b; rewrite b in H0;
                                                                    clear a b;
                                                                      change 2 with (1 + 1) in H0;
                                                                      rewrite <- (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2)) 1 1) in H0;
                                                                        auto with zarith real.
    rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H;
      rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H0;
        rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H;
          rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H0;
            rewrite <- (plus_IZR (Int_part r1 + Int_part r2 + 1) 1) in H0;
              generalize (up_tech (r1 + r2) (Int_part r1 + Int_part r2 + 1) H H0);
                intro; clear H H0; unfold Int_part at 1; omega.
Qed.

(**********)
Lemma plus_Int_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2)%Z.
Proof.
  intros; elim (base_fp r1); elim (base_fp r2); intros; clear H1 H3;
    generalize (Rge_le (frac_part r2) 0 H0); intro; clear H0;
      generalize (Rge_le (frac_part r1) 0 H2); intro; clear H2;
        generalize (Rplus_le_compat_l (frac_part r1) 0 (frac_part r2) H1);
          intro; clear H1; elim (Rplus_ne (frac_part r1)); intros a b;
            rewrite a in H2; clear a b;
              generalize (Rle_trans 0 (frac_part r1) (frac_part r1 + frac_part r2) H0 H2);
                intro; clear H0 H2; unfold frac_part in H, H1; unfold Rminus in H, H1;
                  rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                    in H1; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H1;
                      rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2)
                        in H1;
                        rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H1;
                          rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                            in H1;
                            rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
                              rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)))
                                in H; rewrite (Rplus_comm r2 (- IZR (Int_part r2))) in H;
                                  rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2) in H;
                                    rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2) in H;
                                      rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)))
                                        in H;
                                        rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2))) in H;
                                          generalize
                                            (Rplus_le_compat_l (IZR (Int_part r1) + IZR (Int_part r2)) 0
                                              (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) H1);
                                            intro; clear H1;
                                              generalize
                                                (Rplus_lt_compat_l (IZR (Int_part r1) + IZR (Int_part r2))
                                                  (r1 + r2 + - (IZR (Int_part r1) + IZR (Int_part r2))) 1 H);
                                                intro; clear H;
                                                  rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                    in H1;
                                                    rewrite <-
                                                      (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                        (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                      in H1; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H1;
                                                        elim (Rplus_ne (r1 + r2)); intros a b; rewrite b in H1;
                                                          clear a b;
                                                            rewrite (Rplus_comm (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))))
                                                              in H0;
                                                              rewrite <-
                                                                (Rplus_assoc (IZR (Int_part r1) + IZR (Int_part r2))
                                                                  (- (IZR (Int_part r1) + IZR (Int_part r2))) (r1 + r2))
                                                                in H0; rewrite (Rplus_opp_r (IZR (Int_part r1) + IZR (Int_part r2))) in H0;
                                                                  elim (Rplus_ne (IZR (Int_part r1) + IZR (Int_part r2)));
                                                                    intros a b; rewrite a in H0; clear a b; elim (Rplus_ne (r1 + r2));
                                                                      intros a b; rewrite b in H0; clear a b.
    rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H0;
      rewrite <- (plus_IZR (Int_part r1) (Int_part r2)) in H1;
        rewrite <- (plus_IZR (Int_part r1 + Int_part r2) 1) in H1;
          generalize (up_tech (r1 + r2) (Int_part r1 + Int_part r2) H0 H1);
            intro; clear H0 H1; unfold Int_part at 1;
              omega.
Qed.

(**********)
Lemma plus_frac_part1 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 >= 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2 - 1.
Proof.
  intros; unfold frac_part; generalize (plus_Int_part1 r1 r2 H); intro;
    rewrite H0; rewrite (plus_IZR (Int_part r1 + Int_part r2) 1);
      rewrite (plus_IZR (Int_part r1) (Int_part r2)); simpl;
        unfold Rminus at 3 4;
          rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)));
            rewrite (Rplus_comm r2 (- IZR (Int_part r2)));
              rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2);
                rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2);
                  rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)));
                    rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2)));
                      unfold Rminus;
                        rewrite
                          (Rplus_assoc (r1 + r2) (- (IZR (Int_part r1) + IZR (Int_part r2))) (-(1)))
                          ; rewrite <- (Ropp_plus_distr (IZR (Int_part r1) + IZR (Int_part r2)) 1);
                            trivial with zarith real.
Qed.

(**********)
Lemma plus_frac_part2 :
  forall r1 r2:R,
    frac_part r1 + frac_part r2 < 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2.
Proof.
  intros; unfold frac_part; generalize (plus_Int_part2 r1 r2 H); intro;
    rewrite H0; rewrite (plus_IZR (Int_part r1) (Int_part r2));
      unfold Rminus at 2 3;
        rewrite (Rplus_assoc r1 (- IZR (Int_part r1)) (r2 + - IZR (Int_part r2)));
          rewrite (Rplus_comm r2 (- IZR (Int_part r2)));
            rewrite <- (Rplus_assoc (- IZR (Int_part r1)) (- IZR (Int_part r2)) r2);
              rewrite (Rplus_comm (- IZR (Int_part r1) + - IZR (Int_part r2)) r2);
                rewrite <- (Rplus_assoc r1 r2 (- IZR (Int_part r1) + - IZR (Int_part r2)));
                  rewrite <- (Ropp_plus_distr (IZR (Int_part r1)) (IZR (Int_part r2)));
                    unfold Rminus; trivial with zarith real.
Qed.
