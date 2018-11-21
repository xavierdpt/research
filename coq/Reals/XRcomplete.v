Require Import XRbase.
Require Import XRfunctions.
Require Import XRseries.
Require Import XSeqProp.
Require Import Max.
Require Import Nat.
Local Open Scope XR_scope.

Lemma lt_0_5 : R0 < IZR 5.
Proof.
  apply Rplus_lt_0_compat.
  apply Rlt_0_1.
  apply Rmult_lt_0_compat.
  apply Rplus_lt_0_compat.
  apply Rlt_0_1.
  apply Rlt_0_1.
  apply Rplus_lt_0_compat.
  apply Rlt_0_1.
  apply Rlt_0_1.
Qed.

Lemma neq_5_0 : IZR 5 <> IZR 0.
Proof.
  apply IZR_neq. intro h. inversion h.
Qed.

Lemma technic1 : forall eps, eps / (IZR 5) + (IZR 3) * (eps / (IZR 5)) + eps / (IZR 5) = eps.
Proof.
  intro eps.
  replace eps with ((IZR 5) * (eps / (IZR 5))) at 4.
  {
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ eps).
  rewrite Rplus_assoc.
  rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_l.
  rewrite <- Rmult_plus_distr_l.
  pattern (/ IZR 5) at 1;rewrite <- Rmult_1_l.
  pattern (/ IZR 5) at 3;rewrite <- Rmult_1_l.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- Rmult_plus_distr_r.
  replace R1 with (IZR 1).
  rewrite <- plus_IZR.
  rewrite <- plus_IZR.
  simpl.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  reflexivity.
  exact neq_5_0.
  exact neq_5_0.
  reflexivity.
  }
    unfold Rdiv. (* Rdiv = (r1, r2) => r1 * / r2 *)
    rewrite <- Rmult_assoc. (*  r1 * r2 * r3 = r1 * (r2 * r3) *)
    apply Rinv_r_simpl_m. (* r1 <> 0 -> r1 * r2 * / r1 = r2 *)
    { apply neq_5_0. }
Qed.

Lemma technic2 : forall eps, R0 < eps ->  R0 < eps / (IZR 5).
Proof.
  intros eps h.
  unfold Rdiv. (* Rdiv = (r1, r2) => r1 * / r2 *)
  apply Rmult_lt_0_compat. (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  { apply h. }
  apply Rinv_0_lt_compat. (* 0 < r -> 0 < / r *)
  apply lt_0_5.
Qed.

Local Open Scope nat_scope.

Lemma technic3 : forall N1 N2 N3, max (max N1 N2) N3 >= N2.
Proof.
  intros.
  unfold ge.
  apply le_trans with (max N1 N2). (* n <= m -> m <= p -> n <= p *)
  {
    apply le_max_r. (* n <= max n m *)
  }
  apply le_max_l. (* n <= max n m *)
Qed.

Lemma technic4 : forall N1 N2 N3 k2, max (max N1 N2) N3 + k2 >= N3.
Proof.
intros.
unfold ge.
apply le_trans with (max (max N1 N2) N3).
apply le_max_r.
apply le_plus_l.
Qed.

Local Close Scope nat_scope.

Lemma technic5 : forall x, x / (IZR 3) + x / (IZR 3) + x / (IZR 3) = x.
Proof.
  intro x.
  pattern x at 4; replace x with ((IZR 3) * (x / (IZR 3))).
  {
  unfold Rdiv.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- Rmult_plus_distr_r.
  pattern x at 1 2 3;rewrite <- Rmult_1_r.
  rewrite <- Rmult_plus_distr_l.
  rewrite <- Rmult_plus_distr_l.
  replace R1 with (IZR 1).
  rewrite <- plus_IZR.
  rewrite <- plus_IZR.
  simpl.
  rewrite (Rmult_comm x).
  rewrite Rmult_assoc.
  reflexivity.
  reflexivity.
  }
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  apply Rinv_r_simpl_m.
  replace R0 with (IZR 0).
  apply IZR_neq.
  intro eq;inversion eq.
  reflexivity.
Qed.

Lemma technic6 : forall x, x > R0 -> R0 < x / (IZR 3).
Proof.
  intros x h.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  apply h.
  apply Rinv_0_lt_compat.
  apply Rplus_lt_0_compat.
  apply Rlt_0_1.
  unfold IPR_2.
  apply Rplus_lt_0_compat.
  apply Rlt_0_1.
  apply Rlt_0_1.
Qed.

Lemma technic7 : forall x, (IZR 3) * x = x + x + x.
Proof.
  intro x.
  pattern x at 2 3 4;rewrite <- Rmult_1_l.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- Rmult_plus_distr_r.
  replace R1 with (IZR 1) ; [ idtac | reflexivity ].
  rewrite <- plus_IZR.
  rewrite <- plus_IZR.
  simpl.
  reflexivity.
Qed.

Lemma insert_in_minus : forall a b c, a - c = a - b + (b - c).
Proof.
  intros.
  unfold Rminus.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Theorem R_complete :
  forall U:nat -> R, Cauchy_crit U -> { l:R | Un_cv U l } .
Proof.
  intros.

  (* opp_seq =  n => - U n *)
  (* EUn = exists i, r = Un i *)
  (* bound = exists m, is_upper_bound E m *)

  (* has_lb = bound (EUn (opp_seq Un)) *)
  (* has_ub = bound (EUn Un) *)

  (* sequence_lb : has_lb U -> nat -> R *)
  (* sequence_ub : has_ub U -> nat -> R *)

  (* cauchy_min : Cauchy_crit Un -> has_lb Un *)
  (* cauchy_maj : Cauchy_crit Un -> has_ub Un *)

  set (Uinf := sequence_lb U (cauchy_min U H)). (* nat -> R *)
  set (Usup := sequence_ub U (cauchy_maj U H)). (* nat -> R *)

  (* min_cv : {l : R | Un_cv (sequence_lb Un (cauchy_min Un H)) l} *)
  (* maj_cv : {l : R | Un_cv (sequence_ub Un (cauchy_maj Un pr)) l} *)

  destruct (min_cv U H) as (linf,hinf).
  fold Uinf in hinf.

  destruct (maj_cv U H) as (lsup, hsup).
  fold Usup in hsup.

  cut (lsup = linf).
  {
    intros eq.
    rewrite <- eq in hinf. clear eq. rename lsup into l. clear linf.
    exists l.
    unfold Un_cv.
    intros eps H0.

    cut (R0 < eps / (IZR 3)).
    {

      intro H4.

      unfold Un_cv in hinf.
      unfold Rgt in hinf at 1.
      specialize (hinf (eps / (IZR 3))).
      specialize (hinf H4).
      destruct hinf as [x0 H2].

      unfold Un_cv in hsup.
      unfold Rgt in hsup at 1.
      specialize (hsup (eps / (IZR 3))).
      specialize (hsup H4).
      destruct hsup as [x H1].

      exists (max x x0).
      intros n H3.
      unfold R_dist.

      apply Rle_lt_trans with (Rabs (U n - Uinf n) + Rabs (Uinf n - l)).
      {
        rewrite (insert_in_minus _ (Uinf n) _).
        apply Rabs_triang.
      }
      apply Rle_lt_trans with (Rabs (Usup n - Uinf n) + Rabs (Uinf n - l)).
      {
        rewrite <- (Rplus_comm (Rabs (Uinf n - l))).
        rewrite <- (Rplus_comm (Rabs (Uinf n - l))).
        apply Rplus_le_compat_l.
        rewrite Rabs_right. (* r >= 0 -> Rabs r = r *)
        rewrite Rabs_right.
        {
          unfold Rminus.
          rewrite <- (Rplus_comm (- Uinf n)).
          rewrite <- (Rplus_comm (- Uinf n)).
          apply Rplus_le_compat_l.

          (* Vn_Un_Wn_order :
              V : has_ub Un /\ W : has_lb Un
             sequence_lb Un V n <= U n <= sequence_ub Un W n
          *)
          destruct (Vn_Un_Wn_order U (cauchy_maj U H) (cauchy_min U H) n) as [H5 H8].
          fold Uinf in H5.
          fold Usup in H8.

          apply H8.
        }
        {
          apply Rle_ge.
          apply Rplus_le_reg_l with (Uinf n).
          rewrite Rplus_0_r.
          rewrite Rplus_minus.

          (* Vn_Un_Wn_order *)
          destruct (Vn_Un_Wn_order U (cauchy_maj U H) (cauchy_min U H) n) as [H5 H6].
          fold Uinf in H5.
          fold Usup in H6.

          apply Rle_trans with (U n).
          apply H5.
          apply H6.
        }
        {
          apply Rle_ge.
          apply Rplus_le_reg_l with (Uinf n).
          rewrite Rplus_0_r.
          rewrite Rplus_minus.

          (* Vn_Un_Wn_order *)
          destruct (Vn_Un_Wn_order U (cauchy_maj U H) (cauchy_min U H) n) as [H5 H6].
          fold Uinf in H5.
          fold Usup in H6.

          apply H5.
        }
      }
      apply Rle_lt_trans with (Rabs (Usup n - l) + Rabs (l - Uinf n) + Rabs (Uinf n - l)).
      {
        rewrite <- (Rplus_comm (Rabs (Uinf n - l))).
        rewrite <- (Rplus_comm (Rabs (Uinf n - l))).
        apply Rplus_le_compat_l.
        rewrite (insert_in_minus (Usup n) l (Uinf n) ).
        apply Rabs_triang.
      }
      apply Rlt_le_trans with (eps / (IZR 3) + eps / (IZR 3) + eps / (IZR 3)).
      {
        apply Rplus_lt_compat.
        apply Rplus_lt_compat.
        {
          unfold R_dist in H1.
          apply H1.
          unfold ge. apply le_trans with (max x x0).
          apply le_max_l.
          apply H3.
        }
        {
          rewrite <- Rabs_Ropp.
          rewrite Ropp_minus_distr.
          unfold R_dist in H2.
          apply H2.
          unfold ge.
          apply le_trans with (max x x0).
          apply le_max_r.
          apply H3.
        }
        unfold R_dist in H2.
        apply H2.
        unfold ge.
        apply le_trans with (max x x0).
        apply le_max_r.
        apply H3.
      }
      right.
      apply technic5.
    }
    apply technic6.
    apply H0.
  }

  apply cond_eq. (* 0 < e -> | x - y | < e ) -> x = y *)
  intros eps H0.
  cut (R0 < eps / (IZR 5)).
  {
    intro H1.
    unfold Un_cv in hsup, hinf.
    unfold R_dist in hsup, hinf.

    specialize (hsup (eps / (IZR 5))).
    specialize (hinf (eps / (IZR 5))).

    specialize (hsup H1).
    specialize (hinf H1).

    destruct hsup as [N1 H4].
    destruct hinf as [N2 H5].

    unfold Cauchy_crit in H.
    unfold R_dist in H.

    destruct (H (eps / (IZR 5)) H1) as [N3 H6].
    set (N := max (max N1 N2) N3).
    apply Rle_lt_trans with (Rabs (lsup - Usup N) + Rabs (Usup N - linf)).
    {
      rewrite (insert_in_minus lsup (Usup N) linf).
      apply Rabs_triang.
    }
    apply Rle_lt_trans with
    (Rabs (lsup - Usup N) + Rabs (Usup N - Uinf N) + Rabs (Uinf N - linf)).
    {
      rewrite Rplus_assoc.
      apply Rplus_le_compat_l.
      rewrite (insert_in_minus (Usup N) (Uinf N) linf).
      apply Rabs_triang.
    }
    rewrite <- technic1.
    {
      apply Rplus_lt_compat.
      apply Rplus_lt_compat.
      {
        rewrite <- Rabs_Ropp.
        rewrite Ropp_minus_distr.
        apply H4.
        unfold ge.
        unfold N.
        apply le_trans with (max N1 N2).
        apply le_max_l.
        apply le_max_l.
      }
      {
        unfold Usup, Uinf.
        unfold sequence_majorant, sequence_minorant.

        (* approx_maj :
          h : has_ub Un 
          0 < eps
          ->  exists k, Rabs (lub Un h - Un k) < eps
        *)
        (* maj_ss : has_ub Un -> has_ub (i => Un (k + i)) *)
          (* cauchy_maj : Cauchy_crit Un -> has_ub Un *)

        assert
          (H7 :=
            approx_maj (fun k:nat => U (N + k)%nat) (maj_ss U N (cauchy_maj U H))).

        assert
          (H8 :=
            approx_min (fun k:nat => U (N + k)%nat) (min_ss U N (cauchy_min U H))).
        cut
          (Usup N =
            majorant (fun k:nat => U (N + k)%nat) (maj_ss U N (cauchy_maj U H))).
        {
          cut
            (Uinf N =
              minorant (fun k:nat => U (N + k)%nat) (min_ss U N (cauchy_min U H))).
          {
            intros H9 H10.
            rewrite <- H9 in H8 |- *.
            rewrite <- H10 in H7 |- *.
            destruct (H7 (eps / (IZR 5)) H1) as [k2 H11].
            destruct (H8 (eps / (IZR 5)) H1) as [k1 H12].

            apply Rle_lt_trans with
              (Rabs (Usup N - U (N + k2)%nat) + Rabs (U (N + k2)%nat - Uinf N)).
            (* r1 <= r2 -> r2 < r3 -> r1 < r3 *)
            {
              rewrite (insert_in_minus (Usup N) (U (N + k2)%nat) (Uinf N)).
              apply Rabs_triang. (* Rabs (a + b) <= Rabs a + Rabs b *)
            }
            apply Rle_lt_trans with
              (Rabs (Usup N - U (N + k2)%nat) + Rabs (U (N + k2)%nat - U (N + k1)%nat) +
                Rabs (U (N + k1)%nat - Uinf N)). (* r1 <= r2 -> r2 < r3 -> r1 < r3 *)
            {
              rewrite Rplus_assoc. (*  r1 + r2 + r3 = r1 + (r2 + r3) *)
              apply Rplus_le_compat_l. (* r1 <= r2 -> r + r1 <= r + r2 *)
              rewrite (insert_in_minus (U (N + k2)%nat) (U (N + k1)%nat) (Uinf N)).
              apply Rabs_triang. (* Rabs (a + b) <= Rabs a + Rabs b *)
            }
            rewrite technic7.
            apply Rplus_lt_compat. (* r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4 *)
            apply Rplus_lt_compat. (* r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4 *)
            {
              apply H11.
            }
            {
              apply H6.
              { unfold N. apply technic4. }
              { unfold N. apply technic4. }
            }
            rewrite <- Rabs_Ropp. (* Rabs (- x) = Rabs x *)
            replace
            (- (U (N + k1)%nat - Uinf N)) with
            (Uinf N - U (N + k1)%nat).
            { apply H12. }
            {
			unfold Rminus.
			rewrite Ropp_plus_distr.
			rewrite Ropp_involutive.
			rewrite Rplus_comm.
			reflexivity.
			}
          }
          unfold Uinf. unfold sequence_lb.
          reflexivity.
        }
        unfold Usup. unfold sequence_ub.
        reflexivity.
      }
      apply H5.
      unfold N.
      apply technic3.
    }
  }
  apply technic2.
  apply H0.
Qed.