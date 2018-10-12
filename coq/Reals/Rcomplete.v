Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import SeqProp.
Require Import Max.
Require Import Nat.
Local Open Scope R_scope.

Lemma lt_0_5 : 0 < 5.
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

Lemma neq_5_0 : 5 <> 0.
Proof.
  apply IZR_neq. intro h. inversion h.
Qed.

Lemma technic1 : forall eps, eps / 5 + 3 * (eps / 5) + eps / 5 = eps.
Proof.
  intro eps.
  replace eps with (5 * (eps / 5)) at 4.
  { ring. (* TODO *) }
    unfold Rdiv. (* Rdiv = (r1, r2) => r1 * / r2 *)
    rewrite <- Rmult_assoc. (*  r1 * r2 * r3 = r1 * (r2 * r3) *)
    apply Rinv_r_simpl_m. (* r1 <> 0 -> r1 * r2 * / r1 = r2 *)
    { apply neq_5_0. }
Qed.

Lemma technic2 : forall eps, 0 < eps ->  0 < eps / 5.
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
    unfold Un_cv in hsup, hinf.
    cut (0 < eps / 3).
    {
      intro H4.
      elim (hsup (eps / 3) H4). intros x H1.
      elim (hinf (eps / 3) H4). intros x0 H2.
      exists (max x x0).
      intros n H3.
      unfold R_dist.

      apply Rle_lt_trans with (Rabs (U n - Uinf n) + Rabs (Uinf n - l)).
      {
        replace (U n - l) with (U n - Uinf n + (Uinf n - l));
        [ apply Rabs_triang | ring ].
      }
      apply Rle_lt_trans with (Rabs (Usup n - Uinf n) + Rabs (Uinf n - l)).
      {
        do 2 rewrite <- (Rplus_comm (Rabs (Uinf n - l))).
        apply Rplus_le_compat_l.
        repeat rewrite Rabs_right.
        {
          unfold Rminus; do 2 rewrite <- (Rplus_comm (- Uinf n));
            apply Rplus_le_compat_l.
          assert (H8 := Vn_Un_Wn_order U (cauchy_maj U H) (cauchy_min U H)).
          fold Uinf Usup in H8.
          elim (H8 n); intros.
          assumption.
        }
        {
          apply Rle_ge.
          unfold Rminus; apply Rplus_le_reg_l with (Uinf n).
          rewrite Rplus_0_r.
          replace (Uinf n + (Usup n + - Uinf n)) with (Usup n); [ idtac | ring ].
          assert (H8 := Vn_Un_Wn_order U (cauchy_maj U H) (cauchy_min U H)).
          fold Uinf Usup in H8.
          elim (H8 n); intros.
          apply Rle_trans with (U n); assumption.
        }
        {
          apply Rle_ge.
          unfold Rminus; apply Rplus_le_reg_l with (Uinf n).
          rewrite Rplus_0_r.
          replace (Uinf n + (U n + - Uinf n)) with (U n); [ idtac | ring ].
          assert (H8 := Vn_Un_Wn_order U (cauchy_maj U H) (cauchy_min U H)).
          fold Uinf Usup in H8.
          elim (H8 n); intros.
          assumption.
        }
      }
      apply Rle_lt_trans with (Rabs (Usup n - l) + Rabs (l - Uinf n) + Rabs (Uinf n - l)).
      {
        do 2 rewrite <- (Rplus_comm (Rabs (Uinf n - l))).
        apply Rplus_le_compat_l.
        replace (Usup n - Uinf n) with (Usup n - l + (l - Uinf n));
        [ apply Rabs_triang | ring ].
      }
      apply Rlt_le_trans with (eps / 3 + eps / 3 + eps / 3).
      {
        repeat apply Rplus_lt_compat.
        {
          unfold R_dist in H1.
          apply H1.
          unfold ge; apply le_trans with (max x x0).
          apply le_max_l.
          assumption.
        }
        {
          rewrite <- Rabs_Ropp.
          replace (- (l - Uinf n)) with (Uinf n - l); [ idtac | ring ].
          unfold R_dist in H3.
          apply H2.
          unfold ge; apply le_trans with (max x x0).
          apply le_max_r.
          assumption.
        }
        unfold R_dist in H3.
        apply H2.
        unfold ge; apply le_trans with (max x x0).
        apply le_max_r.
        assumption.
      }
      right.
      pattern eps at 4; replace eps with (3 * (eps / 3)).
      ring.
      unfold Rdiv; rewrite <- Rmult_assoc; apply Rinv_r_simpl_m; discrR.
    }
    unfold Rdiv; apply Rmult_lt_0_compat;
      [ assumption | apply Rinv_0_lt_compat; prove_sup0 ].
  }
  apply cond_eq.
  intros.
  cut (0 < eps / 5).
  {
    intro.
    unfold Un_cv in hsup; unfold Un_cv in hinf.
    unfold R_dist in hsup; unfold R_dist in hinf.
    elim (hsup (eps / 5) H1); intros N1 H4.
    elim (hinf (eps / 5) H1); intros N2 H5.
    unfold Cauchy_crit in H.
    unfold R_dist in H.
    elim (H (eps / 5) H1); intros N3 H6.
    set (N := max (max N1 N2) N3).
    apply Rle_lt_trans with (Rabs (lsup - Usup N) + Rabs (Usup N - linf)).
    {
      replace (lsup - linf) with (lsup - Usup N + (Usup N - linf)); [ apply Rabs_triang | ring ].
    }
    apply Rle_lt_trans with
    (Rabs (lsup - Usup N) + Rabs (Usup N - Uinf N) + Rabs (Uinf N - linf)).
    {
      rewrite Rplus_assoc.
      apply Rplus_le_compat_l.
      replace (
        Usup N - linf
      ) with (
        Usup N - Uinf N + (Uinf N - linf)
      ).
      apply Rabs_triang.
      ring.
    }
    rewrite <- technic1.
    {
      apply Rplus_lt_compat.
      apply Rplus_lt_compat.
      {
        rewrite <- Rabs_Ropp.
        replace (- (lsup - Usup N)) with (Usup N - lsup).
        apply H4.
        unfold ge, N.
        apply le_trans with (max N1 N2).
        apply le_max_l.
        apply le_max_l.
        ring.
      }
      {
        unfold Usup, Uinf.
        unfold sequence_majorant, sequence_minorant.
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
            elim (H7 (eps / 5) H1). intros k2 H11.
            elim (H8 (eps / 5) H1). intros k1 H12.
            apply Rle_lt_trans with
              (Rabs (Usup N - U (N + k2)%nat) + Rabs (U (N + k2)%nat - Uinf N)).
            (* r1 <= r2 -> r2 < r3 -> r1 < r3 *)
            {
              replace (
                Usup N - Uinf N
              ) with (
                Usup N - U (N + k2)%nat + (U (N + k2)%nat - Uinf N)
              ).
              {
                apply Rabs_triang. (* Rabs (a + b) <= Rabs a + Rabs b *)
              }
              ring.
            }
            apply Rle_lt_trans with
              (Rabs (Usup N - U (N + k2)%nat) + Rabs (U (N + k2)%nat - U (N + k1)%nat) +
                Rabs (U (N + k1)%nat - Uinf N)). (* r1 <= r2 -> r2 < r3 -> r1 < r3 *)
            {
              rewrite Rplus_assoc. (*  r1 + r2 + r3 = r1 + (r2 + r3) *)
              apply Rplus_le_compat_l. (* r1 <= r2 -> r + r1 <= r + r2 *)
              replace (
                U (N + k2)%nat - Uinf N
              ) with (
                U (N + k2)%nat - U (N + k1)%nat + (U (N + k1)%nat - Uinf N)
              ).
              {
                apply Rabs_triang. (* Rabs (a + b) <= Rabs a + Rabs b *)
              }
              ring.
            }
            replace (
              3 * (eps / 5)
            ) with (
              eps / 5 + eps / 5 + eps / 5
            ).
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
            { ring. }
            { ring. }
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