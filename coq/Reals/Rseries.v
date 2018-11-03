Require Import Rbase.
Require Import Rfunctions.
Require Import Compare.
Local Open Scope R_scope.

Implicit Type r : R.

Section sequence.

  Fixpoint Rmax_N (U:nat->R) (n:nat) : R :=
    match n with
      | O => U 0%nat
      | S n => Rmax (U (S n)) (Rmax_N U n)
    end.

  Definition EUn (U:nat->R) (r:R) : Prop :=  exists n : nat, r = U n.

  Definition Un_cv (U:nat->R) (l:R) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> R_dist (U n) l < eps).

  Definition Cauchy_crit (U : nat -> R) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat,
        (forall n m:nat,
          (n >= N)%nat -> (m >= N)%nat -> R_dist (U n) (U m) < eps).

  Definition Un_growing (U : nat -> R) : Prop := forall n:nat, U n <= U (S n).

  Lemma EUn_noempty : forall (U : nat -> R), exists r : R, EUn U r.
  Proof.
    intro U.
    exists (U 0%nat).
    unfold EUn.
    exists 0%nat.
    reflexivity.
  Qed.

  Lemma Un_in_EUn : forall (U : nat -> R) (n:nat), EUn U (U n).
  Proof.
    intros U n.
    unfold EUn.
    exists n.
    reflexivity.
  Qed.

  Lemma Un_bound_imp :
    forall (U : nat -> R)  (x:R), (forall n:nat, U n <= x) -> is_upper_bound (EUn U) x.
  Proof.
    intros U x H.
    unfold is_upper_bound.
    intros xn [n eq].
    subst xn.
    apply H.
  Qed.

  Lemma growing_prop :
    forall (U : nat -> R) (n m:nat), Un_growing U -> (n >= m)%nat -> U n >= U m.
  Proof.
    intros U n m hu hnm.
    unfold ge in hnm. apply Rle_ge.
    induction hnm as [ | n hmn i ].
    { right. reflexivity. }
    {
      unfold Un_growing in hu.
      apply Rle_trans with (U n).
      { exact i. }
      { apply hu. }
    }
  Qed.

  (* stopped here *)

  Remark Hi2pn: forall n, 0 < (/ 2)^n.
  Proof.
    intros n.
    apply pow_lt.
    apply Rinv_0_lt_compat.
    apply IZR_lt.
    constructor.
  Qed.


  (* This is the old crit test *)
  Definition cv_crit_test (u : nat->R ) (l e : R) (n:nat) := if Rle_lt_dec (u n) (l - e) then false else true.

  (* And the old crit sum as a fixpoint *)
  Fixpoint cv_crit_sum (u : nat->R ) (l e : R) (n:nat) := match n with
    | O => 0
    | S n' => cv_crit_sum u l e n' +
      if cv_crit_test u l e n' then (/ 2)^n else 0
    end.


  (* This is an equivalent inductive relation  for crit sum and test *)
  Inductive cv_crit_sum_r (u : nat->R ) (l e : R) : nat -> R -> Prop :=
  | crit_O : cv_crit_sum_r u l e 0%nat 0
  | crit_t : forall (n:nat) (r:R),
      (l - e < u n) ->
      cv_crit_sum_r u l e n r ->
      cv_crit_sum_r u l e (S n) ( r + (/ 2)^(S n))
  | crit_f : forall (n:nat) (r:R),
      ( u n <= l - e) ->
      cv_crit_sum_r u l e n r ->
      cv_crit_sum_r u l e (S n) r
  .

  Remark Rlt_0_half : 0 < / 2.
  Proof.
    apply Rinv_0_lt_compat.
    apply Rlt_0_2.
  Qed.

  Remark Rlt_half_1 : / 2 < 1.
  Proof.
    rewrite <- Rinv_1.
    apply Rinv_lt_contravar.
    rewrite Rmult_1_l. apply Rlt_0_2.
    pattern 2;rewrite <- Rmult_1_r. rewrite double.
    pattern 1 at 1;rewrite <- Rplus_0_r. apply Rplus_lt_compat_l.
    apply Rlt_0_1.
  Qed.

  Remark half_half :/ 2 + / 2 = 1.
  Proof.
    pattern (/ 2);rewrite <- Rmult_1_r.
    rewrite <- Rmult_plus_distr_l.
    rewrite <- double.
    rewrite Rmult_1_r.
    rewrite Rinv_l.
    reflexivity.
    intro eq.
    apply Rlt_irrefl with 0.
    pattern 0 at 2;rewrite <- eq.
    apply Rlt_0_2.
  Qed.

  Lemma practice1 : forall u l e,  cv_crit_sum_r u l e 0 0.
  Proof.
    intros.
    constructor.
  Qed.

  (* crit depends on l-e. We show the order of crit_sum depends on the size of l-e *)
  Lemma practice2 : forall u l ex ey n x y,
    l - ex > l - ey -> 
    cv_crit_sum_r u l ex n x ->
    cv_crit_sum_r u l ey n y ->
    x <= y.
  Proof.
    intros u l ex ey n x y.
    intro h.
    intros hx hy.
    generalize dependent y.
    generalize dependent x.
    induction n as [ | n i ].
    {
      intros x hx y hy.
      inversion hx. subst x.
      inversion hy. subst y.
      right. reflexivity.
    }
    {
      intros x hx y hy.
      inversion hx;clear hx.
      {
        subst n0 x.
        rename r into x.
        rename H1 into hx.
        inversion hy;clear hy.
        {
          subst n0 y.
          rename r into y.
          rename H2 into hy.
          apply Rplus_le_compat_r.
          apply i. assumption. assumption.
        }
        {
          subst n0 r.
          exfalso.
          clear - h H0 H1.
          destruct H1.
          {
            apply Rlt_irrefl with (u n).
            apply Rlt_trans with (l-ey).
            assumption.
            apply Rlt_trans with (l-ex);assumption.
          }
          { rewrite H in H0. clear H. apply Rlt_irrefl with (l-ex). apply Rlt_trans with (l-ey);assumption. }
        }
      }
      {
        subst n0 r.
        inversion hy;clear hy.
        {
          subst n0 y.
          rename r into y.
          apply Rle_trans with y.
          { apply i. assumption. assumption. }
          {
            pattern y at 1;rewrite <- Rplus_0_r.
            apply Rplus_le_compat_l.
            apply pow_le.
            left. exact Rlt_0_half.
          }
        }
        {
          subst n0 r.
          apply i;assumption.
        }
      }
    }
  Qed.

  Lemma practice3 : forall u l e,
    (forall n, u n <= l - e) ->
    forall n, cv_crit_sum_r u l e n 0.
  Proof.
    intros u l e h n.
    induction n as [ | n i ].
    constructor.
    apply crit_f. apply h. exact i.
  Qed.


  (* This is the proof that both definitions are equivalent *)
  Remark cv_crit_equiv : forall (u : nat->R ) (l e : R) (n:nat) (r:R),
    cv_crit_sum_r u l e n r <-> cv_crit_sum u l e n = r.
  intros u l e n r.
  split.
  {
    intro h.
    induction h.
    { simpl. reflexivity. }
    { simpl.
      rewrite IHh.
      destruct (cv_crit_test u l e n) eqn:eqt.
      { reflexivity. }
      {
        rewrite Rplus_0_r.
        unfold cv_crit_test in eqt.
        destruct (Rle_lt_dec (u n) (l-e)).
        { destruct r0.
          { exfalso. apply Rlt_irrefl with (l-e). apply Rlt_trans with (u n);assumption. }
          { rewrite H0 in H. apply Rlt_irrefl in H. contradiction. }
        }
        { inversion eqt. }
      }
    }
    {
      simpl.
      rewrite IHh.
      unfold cv_crit_test.
      destruct (Rle_lt_dec (u n) (l-e)).
      { rewrite Rplus_0_r. reflexivity. }
      { exfalso. destruct H.
        { apply Rlt_irrefl with (u n). apply Rlt_trans with (l-e);assumption. }
        { rewrite H in r0. apply Rlt_irrefl in r0. contradiction. }
      }
    }
  }
  {
    intro h. generalize dependent r.
    induction n as [ | n i ].
    { intros r h. simpl in h. subst r. constructor. }
    { intros r h. simpl in h.
      unfold cv_crit_test in h.
      destruct (Rle_lt_dec (u n) (l-e)).
      {
        apply crit_f. exact r0.
        apply i. rewrite Rplus_0_r in h. exact h.
      }
      {
        pose (ccs := cv_crit_sum u l e n).
        fold ccs in h, i.
        rewrite <- h.
        apply crit_t.
        exact r0.
        apply i.
        reflexivity.
      }
    }
  }
  Qed.

  Lemma crit_bound_fix : forall (u : nat -> R) (l e : R) (m n : nat),
    cv_crit_sum u l e m <= cv_crit_sum u l e (m + n) <= cv_crit_sum u l e m + (/ 2) ^ m - (/ 2) ^ (m + n).
  Proof.
      intros u l e m.
      induction n as [ | n i ].
      {
        rewrite<- plus_n_O.
        ring_simplify (cv_crit_sum u l e m + (/ 2) ^ m - (/ 2) ^ m).
        split ; apply Rle_refl.
      }
      {
        rewrite <- plus_n_Sm.
        simpl.
        split.
        {
          apply Rle_trans with (cv_crit_sum u l e (m + n)%nat + 0).
          {
            rewrite Rplus_0_r.
            apply i.
          }
          {
            apply Rplus_le_compat_l.
            case (cv_crit_test u l e (m + n)%nat).
            {
              apply Rlt_le.
              exact (Hi2pn (S (m + n))).
            }
            {
              apply Rle_refl.
            }
          }
        }
        {
          apply Rle_trans with (cv_crit_sum u l e  (m + n)%nat + / 2 * (/ 2) ^ (m + n)).
          {
            apply Rplus_le_compat_l.
            case (cv_crit_test u l e (m + n)%nat).
            {
              apply Rle_refl.
            }
            {
              apply Rlt_le.
              exact (Hi2pn (S (m + n))).
            }
          }
          {
            apply Rplus_le_reg_r with (-(/ 2 * (/ 2) ^ (m + n))).
            rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
            apply Rle_trans with (1 := proj2 i).
            apply Req_le.
            field.
          }
        }
      }
  Qed.


  Lemma cv_crit_sum_r_inj : forall (u : nat -> R) (l e : R) (n:nat) (r r' : R),
    cv_crit_sum_r u l e n r ->
    cv_crit_sum_r u l e n r' ->
    r = r' .
  Proof.
    intros u l e n r r' hr.
    generalize dependent r'.
    induction hr.
    {
      intros r' hr'. inversion hr'. reflexivity.
    }
    {
      intros r' hr'. inversion hr'.
      {
        subst n0.
        apply Rplus_eq_compat_r.
        apply IHhr.
        assumption.
      }
      {
        exfalso.
        destruct H1.
        apply Rlt_irrefl with (u n). apply Rlt_trans with (l-e);assumption.
        rewrite H1 in H. apply Rlt_irrefl in H. contradiction.
      }
    }
    {
      intros r' hr'.
      inversion hr'.
      {
        exfalso.
        destruct H.
        apply Rlt_irrefl with (u n). apply Rlt_trans with (l-e);assumption.
        rewrite H in H1. apply Rlt_irrefl in H1. contradiction.
      }
      {
        apply IHhr.
        assumption.
      }
    }
  Qed.

  Lemma crit_Sn : forall u l e n y,
    cv_crit_sum_r u l e (S n) y ->
    (u n <= l - e /\ cv_crit_sum_r u l e n y) \/ (l - e < u n /\ cv_crit_sum_r u l e n (y - (/ 2) ^ (S n))).
  Proof.
    intros u l e n y hy.
    inversion hy;clear hy.
    { subst y n0.
      right. split. assumption.
      unfold Rminus. rewrite Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_r.
      assumption.
    }
    { subst n0 r. left. split;assumption. }
  Qed.



  Lemma crit_bound : forall (u : nat -> R) (l e : R) (m n : nat) (x y:R),
    cv_crit_sum_r u l e m x ->
    cv_crit_sum_r u l e (m + n) y ->
    x <= y <= x + (/ 2) ^ m - (/ 2) ^ (m + n).
  Proof.
    intros u l e m n x y hx hy.
    generalize dependent m.
    generalize dependent y.
    generalize dependent x.
    induction n as [ | n i ].
    {
      intros x y m hx hy.
      rewrite plus_comm in hy.
      simpl in hy.
      rewrite plus_comm.
      simpl.
      unfold Rminus.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_r.
      {
        inversion hx.
        {
          subst x.
          subst m.
          inversion hy.
          subst y.
          split;right;reflexivity.
        }
        {
          subst x.
          subst m.
          simpl.
          simpl in hx.
          inversion hy.
          {
            subst y.
            subst n0.
            simpl.
            simpl in hy.
            split.
            {
              right.
              apply (cv_crit_sum_r_inj u l e (S n)).
              assumption.
              assumption.
            }
            {
              right.
              apply (cv_crit_sum_r_inj u l e (S n)).
              assumption.
              assumption.
            }
          }
          {
            subst n. subst y. exfalso.
            destruct H2. apply Rlt_irrefl with (u n0). apply Rlt_trans with (l-e);assumption.
            rewrite H1 in H. apply Rlt_irrefl in H. contradiction.
          }
        }
        {
          subst x.
          subst m.
          inversion hy.
          {
            subst y.
            subst n0.
            exfalso.
            destruct H. apply Rlt_irrefl with (u n). apply Rlt_trans with (l-e);assumption.
            rewrite H in H2. apply Rlt_irrefl in H2. contradiction.
          }
          {
            subst y. subst n0. split.
            { right. apply (cv_crit_sum_r_inj u l e (S n)). assumption. assumption. }
            { right. apply (cv_crit_sum_r_inj u l e (S n)). assumption. assumption. }
          }
        }
      }
    }
    {
      intros x y m hx hy.
      rewrite <- plus_n_Sm in hy.
      inversion hy;clear hy.
      {
        subst n0 y.
        rename r into y;rename H1 into hy.
        specialize (i x y m hx hy).
        destruct i.
        split.
        {
          apply Rle_trans with y.
          assumption.
          pattern y at 1;rewrite <- Rplus_0_r. apply Rplus_le_compat_l.
          apply pow_le. left. apply Rlt_0_half.
        }
        {
          simpl.
          apply Rplus_le_reg_r with (-(/ 2 * (/ 2) ^ (m + n))).
          rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r.
          rewrite <- plus_n_Sm. simpl.
          unfold Rminus.
          rewrite Rplus_assoc.
          rewrite <- Ropp_plus_distr.
          rewrite <- Rmult_plus_distr_r.
          rewrite half_half.
          rewrite Rmult_1_l.
          assumption.
        }
      }
      {
        subst y n0. rename r into y. rename H1 into hy.
        specialize (i x y m hx hy).
        destruct i.
        split. assumption.
        apply Rle_trans with (x + (/ 2) ^ m - (/ 2) ^ (m + n)).
        assumption.
        unfold Rminus. apply Rplus_le_compat_l.
        apply Ropp_le_contravar.
        rewrite <- plus_n_Sm. simpl.
        pattern ((/ 2) ^ (m + n)) at 2;rewrite <- Rmult_1_l.
        apply Rmult_le_compat_r.
        apply pow_le.
        left. apply Rlt_0_half.
        left. apply Rlt_half_1.
      }
    }
  Qed.

  Lemma crit_bound_O : forall u l e n x, cv_crit_sum_r u l e n x ->  0 <= x <= 1 - (/2)^n.
  Proof.
    intros u l e n x h.
    generalize (crit_bound u l e 0 n 0 x); intro cb.
    pattern 1;rewrite <- Rplus_0_l.
    rewrite <- pow_O with (/ 2).
    rewrite plus_n_O with n.
    rewrite plus_comm.
    apply cb.
    - constructor.
    - simpl. assumption.
  Qed.

  Lemma crit_exist : forall u l e n, exists x, cv_crit_sum_r u l e n x.
  Proof.
    intros u l e n.
    induction n as [ | n i ].
    {
      exists 0. constructor.
    }
    {
      destruct i as [ x i ].
      destruct (Rtotal_order (u n) (l-e)).
      exists x. apply crit_f. left. assumption. assumption.
      destruct H.
      exists x. apply crit_f. right. assumption. assumption.
      exists (x+ (/ 2) ^ S n). apply crit_t. assumption. assumption.
    }
  Qed.

  Lemma youpi : forall (u : nat -> R) (l e : R),
    is_upper_bound (fun x : R => exists n : nat, cv_crit_sum_r u l e n x) 0 ->
    forall n : nat, cv_crit_sum_r u l e n 0.
  Proof.
    intros u l e h n.
    destruct (crit_exist u l e n).
    assert (eq:x = 0).
    {
      apply Rle_antisym.
      unfold is_upper_bound in h. apply h.
      exists n. assumption.
      apply (crit_bound_O u l e n x).
      assumption.
    }
    subst x.
    assumption.
  Qed.

  Definition fcrit1 u l e x := exists n : nat, cv_crit_sum_r u l e n x.

  Lemma crit_pos : forall u l e n x, cv_crit_sum_r u l e n x -> 0 <= x.
  Proof.
    intros u l e n x h.
    generalize dependent x.
    induction n as [ | n i ].
    { intros x h. inversion h. subst x. right. reflexivity. }
    {
      intros x h.
      inversion h;clear h.
      {
        subst x n0.
        apply Rle_trans with r.
        { apply i. assumption. }
        {
          pattern r at 1;rewrite <- Rplus_0_r.
          apply Rplus_le_compat_l.
          apply pow_le.
          left.
          exact Rlt_0_half.
        }
      }
      { subst x n0. apply i. assumption. }
    }
    Qed.

  Lemma crit_technic_1 : forall (u : nat -> R) (l e : R),
    (forall n : nat, cv_crit_sum_r u l e n 0) ->
    forall n : nat, u n <= l - e.
  Proof.
    intros u l e h n.
    specialize (h (S n)).
    inversion h;clear h.
    {
      subst n0.
      rename H0 into eq.
      apply (Rplus_eq_compat_r (-(/ 2 * (/ 2) ^ n))) in eq.
      rewrite Rplus_assoc in eq.
      rewrite Rplus_opp_r in eq.
      rewrite Rplus_0_r in eq.
      rewrite Rplus_0_l in eq.
      subst r.
      rename H2 into h.
      apply crit_pos in h.
      exfalso. clear -h.
      destruct h.
      {
        apply Rlt_irrefl with 0.
        apply Rlt_trans with (- (/ 2 * (/ 2) ^ n)).
        { assumption. }
        {
          rewrite <- Ropp_0.
          apply Ropp_lt_contravar.
          rewrite tech_pow_Rmult.
          apply pow_lt.
          exact Rlt_0_half.
        }
      }
      {
        apply Rlt_irrefl with 0.
        pattern 0 at 1;rewrite H.
        rewrite <- Ropp_0.
        apply Ropp_lt_contravar.
        rewrite tech_pow_Rmult.
        apply pow_lt.
        exact Rlt_0_half.
      }
    }
    { assumption. }
    Qed.

  Lemma crit_technic_2: forall (u : nat -> R) (l e : R),
    Un_growing u ->
    forall N : nat, u (S N) <= l - e ->
    u N <= l - e.
  Proof.
    intros u l e hu.
    intros n hn.
    unfold Un_growing in hu.
    apply Rle_trans with (u (S n)).
    - apply hu.
    - assumption.
  Qed.


  Lemma Rlt_abs_half_1 : Rabs (/2) < 1.
  Proof.
    rewrite Rabs_pos_eq.
    - apply Rlt_half_1.
    - left.
      apply Rlt_0_half.
  Qed.

  Lemma crit_technic_3 : forall (u : nat -> R) (l e : R),
    is_upper_bound (fcrit1 u l e) 0 ->
    forall n : nat, cv_crit_sum_r u l e n 0.
  Proof.
    intros u l e h.
    generalize youpi;intro youpi.
    specialize (youpi u l e). intro n.
    unfold is_upper_bound in h.
    apply youpi.
    unfold is_upper_bound.
    intros iti oto.
    destruct oto as [ zim zam ].
    apply h.
    exists zim. assumption.
  Qed.


  Lemma crit_technic_4_fix : forall (u : nat -> R) (l e : R), Un_growing u -> forall  (N : nat), u N <= l - e -> cv_crit_sum u l e N = 0.
  Proof.
      intros.
      induction N.
      { easy. }
      {
        simpl.
        generalize crit_technic_2;intro H6.
        specialize (H6 u l e H).
        specialize (H6 N).
        specialize (H6 H0).
        rewrite (IHN H6), Rplus_0_l.
        unfold cv_crit_test.
        destruct Rle_lt_dec as [Hle|Hlt].
        {
          apply eq_refl.
        }
        now elim Rlt_not_le with (1 := Hlt).
      }
  Qed.


  Lemma crit_technic_4 : forall (u : nat -> R) (l e : R),
    Un_growing u ->
    forall  (N : nat), u N <= l - e ->
    cv_crit_sum_r u l e N 0.
  Proof.
      intros.
      induction N.
      { constructor. }
      {
        simpl.
        generalize crit_technic_2;intro H6.
        specialize (H6 u l e H).
        specialize (H6 N).
        specialize (H6 H0).
        apply crit_f.
        exact H6.
        apply IHN.
        exact H6.
      }
  Qed.

  Lemma crit_bounded : forall u l e, bound (fcrit1 u l e).
  Proof.
    intros u l e.
    unfold bound.
    exists 1.
    unfold is_upper_bound.
    intros x h.
    unfold fcrit1 in h.
    destruct h as [n h].
    apply Rle_trans with (1-(/2)^n).
    {
      generalize crit_bound_O;intro cb.
      specialize (cb u l e n x).
      specialize (cb h).
      apply proj2 in cb.
      exact cb.
    }
    {
      pattern 1 at 2;rewrite <- Rplus_0_r.
      apply Rplus_le_compat_l.
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      left.
      apply pow_lt.
      exact Rlt_0_half.
    }
  Qed.

  Lemma crit_exists : forall u l e, exists x : R, fcrit1 u l e x.
  Proof.
    intros u l e.
    exists 0.
    unfold fcrit1.
    exists 0%nat.
    constructor.
  Qed.

  Lemma crit_technic_5_neg : forall (u : nat -> R) (l e m : R),
    is_lub (fcrit1 u l e) m ->
    m < 0 ->
    False.
  Proof.
    intros u l e m hub h.
    destruct hub as [ hubl hubr ].
    unfold is_upper_bound in hubl.
    apply Rlt_not_le in h.
    apply h.
    apply hubl.
    unfold fcrit1.
    exists 0%nat.
    constructor.
  Qed.

  Lemma crit_technic_b : forall (u : nat -> R) (l e : R),
    e > 0 ->
    is_lub (EUn u) l ->
    (forall n : nat, u n <= l - e) ->
    False.
  Proof.
    intros u l e he hlub h.
    unfold is_lub in hlub.
    unfold is_upper_bound in hlub.
    unfold EUn in hlub.
    destruct hlub as [hlubl hlubr].
    specialize (hlubr (l-e)).
    apply (Rle_not_lt (l-e) l).
    2:{
      pattern l at 2;rewrite <- Rplus_0_r.
      unfold Rminus.
      apply Rplus_lt_compat_l.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      apply Rgt_lt in he.
      exact he.
    }
    {
      apply hlubr.
      intros x hex.
      destruct hex as [n eq].
      subst x.
      apply h.
    }
  Qed.

  Lemma crit_technic_c : forall (u : nat -> R) (l e m : R),
    Un_growing u ->
    0 < m ->
    (forall b : R, is_upper_bound (fcrit1 u l e) b -> m <= b) ->
    exists N : nat, u N > l - e.
  Proof.
    intros u l e m hu Hm Hm2.
    generalize Rlt_abs_half_1;intro H0.
    destruct (pow_lt_1_zero (/2) H0 m Hm) as [N H4].
    exists N.
    apply Rnot_le_lt.
    intros H5.
    apply Rlt_not_le with (1 := H4 _ (le_refl _)).
    rewrite Rabs_pos_eq.
    {
      apply Hm2.
      intros x (n, H6).
      rewrite cv_crit_equiv in H6.
      rewrite <- H6. clear x H6.

      generalize crit_technic_4_fix;intro Hs.
      specialize (Hs u l e hu).
      specialize (Hs N H5).

      destruct (le_or_lt N n) as [Hn|Hn].
      {
        rewrite le_plus_minus with (1 := Hn).
        apply Rle_trans with (  cv_crit_sum u l e N + (/ 2) ^ N - (/ 2) ^ (N + (n - N)) ).
        apply (crit_bound_fix u l e).
        rewrite Hs.
        rewrite Rplus_0_l.
        pose (k := (N + (n - N))%nat).
        fold k.
        pose (p2N:=(/2)^N).
        pose (p2k:=(/2)^k).
        fold p2N. fold p2k.
        left.
        apply Rplus_lt_reg_l with (p2k - p2N).
        unfold Rminus.
        repeat (rewrite Rplus_assoc).
        rewrite (Rplus_comm).
        repeat (rewrite <- Rplus_assoc).
        rewrite Rplus_opp_l.
        rewrite Rplus_0_l.
        rewrite Rplus_opp_l.
        repeat (rewrite Rplus_assoc).
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        unfold p2k.
        apply Hi2pn.
      }
      apply Rle_trans with (cv_crit_sum u l e N).
      {
        rewrite le_plus_minus with (1 := Hn).
        rewrite plus_Snm_nSm.
        apply (crit_bound_fix u l e).
      }
      {
        rewrite Hs.
        left.
        apply pow_lt.
        apply Rlt_0_half.
      }
    }
  left.
  apply Hi2pn.
Qed.

  Lemma crit_technic_5 : forall (u : nat -> R) (l e : R),
    Un_growing u -> is_lub (EUn u) l -> e > 0 ->
    exists N : nat, u N > l - e.
  Proof.
      intros u l e hu H  he.
      generalize completeness;intro hc.
      specialize (hc (fcrit1 u l e)).
      specialize (hc (crit_bounded u l e)).
      specialize (hc (crit_exists u l e)).
      destruct hc as [ m hlub].
      generalize hlub;intro hlub'.
      destruct hlub as [Hm1 Hm2].
      rename hlub' into hlub.
      {
        destruct (Rle_or_lt m 0) as [[Hm|Hm]|Hm].
        { (* m < 0 *)
          exfalso.
          apply (crit_technic_5_neg u l e m).
          exact hlub.
          exact Hm.
        }
        { (* m = 0 *)
          subst m.
          exfalso.
          apply (crit_technic_b u l e).
          { exact he. }
          { exact H. }
          {
            apply crit_technic_1.
(*            apply crit_technic_1_fix. *)
            intros n.
            apply crit_technic_3.
            exact Hm1.
          }
        }
        { (* m > 0 *)
          clear - Hm Hm2 hu.
          apply crit_technic_c with m.
          { exact hu. }
          { exact Hm. }
          { exact Hm2. }
        }
      }
  Qed.

  Lemma Un_cv_crit_lub : forall (U : nat -> R), Un_growing U -> forall l, is_lub (EUn U) l -> Un_cv U l.
  Proof.
    intros u hu l hul.
    unfold Un_cv.
    intros e he.
    unfold R_dist.
    generalize crit_technic_5;intro HE.
    specialize (HE u l e hu hul he).
    destruct HE as [N hun].
    exists N.
    intros n hnN.
    unfold R_dist.
    rewrite Rabs_left1.
    2:{
      unfold Rminus.
      apply Rplus_le_reg_r with l.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_l.
      rewrite Rplus_0_r.
      unfold is_lub in hul.
      apply proj1 in hul.
      unfold is_upper_bound in hul.
      apply hul.
      apply Un_in_EUn.
    }
    {
      apply Rgt_lt in hun.
      rewrite Ropp_minus_distr.
      apply Rplus_lt_reg_l with (-e).
      unfold Rminus.
      rewrite <- Rplus_assoc.
      rewrite (Rplus_comm (-e)).
      rewrite Rplus_opp_l.
      apply Rplus_lt_reg_r with (u n).
      rewrite Rplus_0_l.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_r.
      unfold Rminus in hun.
      apply Rlt_le_trans with (u N).
      { assumption. }
      {
        apply Rge_le.
        apply growing_prop.
        { assumption. }
        { assumption. }
      }
    }
  Qed.

(*********)
  Lemma Un_cv_crit : Un_growing -> bound EUn ->  exists l : R, Un_cv l.
  Proof.
    intros Hug Heub.
    exists (proj1_sig (completeness EUn Heub EUn_noempty)).
    destruct (completeness EUn Heub EUn_noempty) as (l, H).
    now apply Un_cv_crit_lub.
  Qed.

(*********)
  Lemma finite_greater :
    forall N:nat,  exists M : R, (forall n:nat, (n <= N)%nat -> Un n <= M).
  Proof.
    intro; induction  N as [| N HrecN].
    split with (Un 0); intros; rewrite (le_n_O_eq n H);
      apply (Req_le (Un n) (Un n) (eq_refl (Un n))).
    elim HrecN; clear HrecN; intros; split with (Rmax (Un (S N)) x); intros;
      elim (Rmax_Rle (Un (S N)) x (Un n)); intros; clear H1;
        inversion H0.
    rewrite <- H1; rewrite <- H1 in H2;
      apply
        (H2 (or_introl (Un n <= x) (Req_le (Un n) (Un n) (eq_refl (Un n))))).
    apply (H2 (or_intror (Un n <= Un (S N)) (H n H3))).
  Qed.

(*********)
  Lemma cauchy_bound : Cauchy_crit -> bound EUn.
  Proof.
    unfold Cauchy_crit, bound; intros; unfold is_upper_bound;
      unfold Rgt in H; elim (H 1 Rlt_0_1); clear H; intros;
        generalize (H x); intro; generalize (le_dec x); intro;
          elim (finite_greater x); intros; split with (Rmax x0 (Un x + 1));
            clear H; intros; unfold EUn in H; elim H; clear H;
              intros; elim (H1 x2); clear H1; intro y.
    unfold ge in H0; generalize (H0 x2 (le_n x) y); clear H0; intro;
      rewrite <- H in H0; unfold R_dist in H0; elim (Rabs_def2 (Un x - x1) 1 H0);
        clear H0; intros; elim (Rmax_Rle x0 (Un x + 1) x1);
          intros; apply H4; clear H3 H4; right; clear H H0 y;
            apply (Rlt_le x1 (Un x + 1)); generalize (Rlt_minus (-1) (Un x - x1) H1);
              clear H1; intro; apply (Rminus_lt x1 (Un x + 1));
                cut (-1 - (Un x - x1) = x1 - (Un x + 1));
                  [ intro; rewrite H0 in H; assumption | ring ].
    generalize (H2 x2 y); clear H2 H0; intro; rewrite <- H in H0;
      elim (Rmax_Rle x0 (Un x + 1) x1); intros; clear H1;
        apply H2; left; assumption.
  Qed.

End sequence.

(*****************************************************************)
(**  *       Definition of Power Series and properties           *)
(*                                                               *)
(*****************************************************************)

Section Isequence.

(*********)
  Variable An : nat -> R.

(*********)
  Definition Pser (x l:R) : Prop := infinite_sum (fun n:nat => An n * x ^ n) l.

End Isequence.

Lemma GP_infinite :
  forall x:R, Rabs x < 1 -> Pser (fun n:nat => 1) x (/ (1 - x)).
Proof.
  intros; unfold Pser; unfold infinite_sum; intros;
    elim (Req_dec x 0).
  intros; exists 0%nat; intros; rewrite H1; rewrite Rminus_0_r; rewrite Rinv_1;
    cut (sum_f_R0 (fun n0:nat => 1 * 0 ^ n0) n = 1).
  intros; rewrite H3; rewrite R_dist_eq; auto.
  elim n; simpl.
  ring.
  intros; rewrite H3; ring.
  intro; cut (0 < eps * (Rabs (1 - x) * Rabs (/ x))).
  intro; elim (pow_lt_1_zero x H (eps * (Rabs (1 - x) * Rabs (/ x))) H2);
    intro N; intros; exists N; intros;
      cut
        (sum_f_R0 (fun n0:nat => 1 * x ^ n0) n = sum_f_R0 (fun n0:nat => x ^ n0) n).
  intros; rewrite H5;
    apply
      (Rmult_lt_reg_l (Rabs (1 - x))
        (R_dist (sum_f_R0 (fun n0:nat => x ^ n0) n) (/ (1 - x))) eps).
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  unfold R_dist; rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_l.
  cut
    ((1 - x) * sum_f_R0 (fun n0:nat => x ^ n0) n =
      - (sum_f_R0 (fun n0:nat => x ^ n0) n * (x - 1))).
  intro; rewrite H6.
  rewrite GP_finite.
  rewrite Rinv_r.
  cut (- (x ^ (n + 1) - 1) - 1 = - x ^ (n + 1)).
  intro; rewrite H7.
  rewrite Rabs_Ropp; cut ((n + 1)%nat = S n); auto.
  intro H8; rewrite H8; simpl; rewrite Rabs_mult;
    apply
      (Rlt_le_trans (Rabs x * Rabs (x ^ n))
        (Rabs x * (eps * (Rabs (1 - x) * Rabs (/ x)))) (
          Rabs (1 - x) * eps)).
  apply Rmult_lt_compat_l.
  apply Rabs_pos_lt.
  assumption.
  auto.
  cut
    (Rabs x * (eps * (Rabs (1 - x) * Rabs (/ x))) =
      Rabs x * Rabs (/ x) * (eps * Rabs (1 - x))).
  clear H8; intros; rewrite H8; rewrite <- Rabs_mult; rewrite Rinv_r.
  rewrite Rabs_R1; cut (1 * (eps * Rabs (1 - x)) = Rabs (1 - x) * eps).
  intros; rewrite H9; unfold Rle; right; reflexivity.
  ring.
  assumption.
  ring.
  ring.
  ring.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  ring; ring.
  elim n; simpl.
  ring.
  intros; rewrite H5.
  ring.
  apply Rmult_lt_0_compat.
  auto.
  apply Rmult_lt_0_compat.
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  apply Rabs_pos_lt.
  apply Rinv_neq_0_compat.
  assumption.
Qed.

(* Convergence is preserved after shifting the indices. *)
Lemma CV_shift : 
  forall f k l, Un_cv (fun n => f (n + k)%nat) l -> Un_cv f l.
intros f' k l cvfk eps ep; destruct (cvfk eps ep) as [N Pn].
exists (N + k)%nat; intros n nN; assert (tmp: (n = (n - k) + k)%nat).
 rewrite Nat.sub_add;[ | apply le_trans with (N + k)%nat]; auto with arith.
rewrite tmp; apply Pn; apply Nat.le_add_le_sub_r; assumption.
Qed.

Lemma CV_shift' : 
  forall f k l, Un_cv f l -> Un_cv (fun n => f (n + k)%nat) l.
intros f' k l cvf eps ep; destruct (cvf eps ep) as [N Pn].
exists N; intros n nN; apply Pn; auto with arith.
Qed.

(* Growing property is preserved after shifting the indices (one way only) *)

Lemma Un_growing_shift : 
   forall k un, Un_growing un -> Un_growing (fun n => un (n + k)%nat).
Proof.
intros k un P n; apply P.
Qed.
