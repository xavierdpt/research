Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import Max.
Require Import Omega.
Local Open Scope R_scope.

Definition Un_decreasing (u:nat -> R) : Prop :=
  forall n:nat, u (S n) <= u n.

Definition opp_seq (u:nat -> R) (n:nat) : R := - u n.

Definition has_ub (u:nat -> R) : Prop := bound (EUn u).

Definition has_lb (u:nat -> R) : Prop := bound (EUn (opp_seq u)).

Lemma exists_lub : forall (u:nat->R), bound (EUn u) -> { l | is_lub (EUn u) l }.
Proof.
  intros u hb.
  apply completeness.
  { exact hb. }
  { apply EUn_noempty. }
Qed.

Lemma growing_cv :
  forall u:nat -> R, Un_growing u -> has_ub u -> { l:R | Un_cv u l }.
Proof.
  intros u hg hub.
  unfold has_ub in hub.
  destruct (exists_lub u) as [l hlub].
  { exact hub. }
  {
    exists l.
    apply Un_cv_crit_lub.
    { exact hg. }
    { exact hlub. }
  }
Qed.

Lemma decreasing_growing :
  forall u:nat -> R, Un_decreasing u -> Un_growing (opp_seq u).
Proof.
  intros u hdec.
  unfold Un_decreasing in hdec.
  unfold Un_growing.
  intro n.
  specialize (hdec n).
  unfold opp_seq.
  apply Ropp_le_contravar.
  exact hdec.
Qed.

Lemma decreasing_cv :
  forall u:nat -> R, Un_decreasing u -> has_lb u -> { l:R | Un_cv u l }.
Proof.

  intros u hdec hlb.
  unfold has_lb in hlb.
  
  generalize completeness;intro hc.
  specialize (hc (EUn (opp_seq u))).
  specialize (hc hlb);clear hlb.
  specialize (hc (EUn_noempty (opp_seq u))).
  destruct hc as [l hlub].

  exists (-l).

  generalize Un_cv_crit_lub;intro h.
  specialize (h (opp_seq u)).
  apply decreasing_growing in hdec.
  specialize (h hdec);clear hdec.
  specialize (h l).
  specialize (h hlub);clear hlub.

  unfold Un_cv.
  intros e he.

  unfold Un_cv in h.
  specialize (h e he).

  destruct h as [N h].
  exists N.

  intros n hnn.
  specialize (h n hnn);clear hnn.

  unfold opp_seq in h.
  unfold R_dist in h.
  unfold Rminus in h.
  rewrite <- Ropp_plus_distr in h.
  rewrite Rabs_Ropp in h.

  unfold R_dist.
  unfold Rminus.
  rewrite Ropp_involutive.

  exact h.
Qed.

Lemma ub_to_lub :
  forall u:nat -> R, has_ub u -> { l:R | is_lub (EUn u) l }.
Proof.
  intros u h.
  unfold has_ub in h.
  apply completeness.
  { exact h. }
  { apply EUn_noempty. }
Qed.

Lemma lb_to_glb :
  forall u:nat -> R, has_lb u -> { l:R | is_lub (EUn (opp_seq u)) l }.
Proof.
  intros u h.
  unfold has_lb in h.
  apply completeness.
  { exact h. }
  { apply EUn_noempty. }
Qed.

Definition lub (Un:nat -> R) (pr:has_ub Un) : R :=
  let (a,_) := ub_to_lub Un pr in a.

Definition glb (Un:nat -> R) (pr:has_lb Un) : R :=
  let (a,_) := lb_to_glb Un pr in - a.

Notation maj_sup := ub_to_lub (only parsing).
Notation min_inf := lb_to_glb (only parsing).
Notation majorant := lub (only parsing).
Notation minorant := glb (only parsing).

Lemma maj_ss :
  forall (u:nat -> R) (k:nat),
    has_ub u -> has_ub (fun i:nat => u (k + i)%nat).
Proof.
  intros u k h.
  unfold has_ub.
  unfold has_ub in h.
  unfold bound in h.
  unfold bound.
  destruct h as [ M h ].
  exists M.
  unfold is_upper_bound.
  intros x hx.
  unfold is_upper_bound in h.
  apply h.
  unfold EUn in hx.
  destruct hx as [n eq].
  unfold EUn.
  exists (k+n)%nat.
  exact eq.
Qed.

Lemma min_ss :
  forall (u:nat -> R) (k:nat),
    has_lb u -> has_lb (fun i:nat => u (k + i)%nat).
Proof.
  intros u k.
  unfold has_lb.
  unfold bound.
  unfold is_upper_bound.
  unfold EUn.
  unfold opp_seq.
  intros [M h].
  exists M.
  intros x [n eq].
  apply h.
  exists (k+n)%nat.
  exact eq.
Qed.

Definition sequence_ub (Un:nat -> R) (pr:has_ub Un)
  (i:nat) : R := lub (fun k:nat => Un (i + k)%nat) (maj_ss Un i pr).

Definition sequence_lb (Un:nat -> R) (pr:has_lb Un)
  (i:nat) : R := glb (fun k:nat => Un (i + k)%nat) (min_ss Un i pr).

Notation sequence_majorant := sequence_ub (only parsing).
Notation sequence_minorant := sequence_lb (only parsing).

Lemma lub_is_lub : forall f hb, is_lub (EUn f) (lub f hb).
Proof.
  intros f hb.
  unfold lub.
  destruct (ub_to_lub f hb).
  exact i.
Qed.

Lemma lub_unique : forall p l1 l2, is_lub p l1 -> is_lub p l2 -> l1 = l2.
Proof.
  intros p l1 l2 hl1 hl2.
  destruct hl1 as [up1 min1].
  destruct hl2 as [up2 min2].
  apply Rle_antisym.
  {
    apply min1.
    exact up2.
  }
  {
    apply min2.
    exact up1.
  }
Qed.

Lemma Wn_decreasing :
  forall (Un:nat -> R) (pr:has_ub Un), Un_decreasing (sequence_ub Un pr).
Proof.
  intros Un u_has_ub.
  unfold Un_decreasing.
  intro n.
  unfold sequence_ub.

  (* Introduce variables to improve readability *)

  pose (f:=fun k:nat => Un (S n + k)%nat).
  fold f.

  pose (g:=fun k:nat => Un (n + k)%nat).
  fold g.

  pose (hbf := (maj_ss Un (S n) u_has_ub)).
  fold f in hbf.
  fold hbf.

  pose (hbg := (maj_ss Un n u_has_ub)).
  fold g in hbg.
  fold hbg.

  (* upper bound -> there's a least upper bound *)
  destruct (ub_to_lub f hbf) as [ lf hlubf].
  destruct (ub_to_lub g hbg) as [ lg hlubg].

  assert (eqf : lub f hbf = lf).
  {
    apply (lub_unique (EUn f)).
    - apply lub_is_lub.
    - exact hlubf.
  }

  assert (eqg : lub g hbg = lg).
  {
    apply (lub_unique (EUn g)).
    - apply lub_is_lub.
    - exact hlubg.
  }

  (* Now we can get rid of this lub _ _ thing and simplify even more *)
  rewrite eqf.
  rewrite eqg.
  clear eqf eqg hbf hbg u_has_ub.

  destruct hlubf as [lf_up lf_min];clear lf_up.
  destruct hlubg as [lg_up lg_min];clear lg_min.

  apply lf_min;clear lf_min.

  unfold is_upper_bound.
  intros ubf hubf.
  unfold is_upper_bound in lg_up.
  apply lg_up;clear lg_up.

  destruct hubf as [nubf heq].
  subst ubf.
  unfold EUn.
  unfold f.
  unfold g.

  exists (S nubf).

  rewrite plus_Sn_m.
  rewrite <- plus_n_Sm.

  reflexivity.

Qed.

Lemma Vn_growing :
  forall (Un:nat -> R) (pr:has_lb Un), Un_growing (sequence_lb Un pr).
Proof.

  intros u u_has_lb.
  unfold Un_growing.
  intro n.
  unfold sequence_lb.

  pose (f := fun k : nat => u (n + k)%nat).
  fold f.

  pose (g := fun k : nat => u (S n + k)%nat).
  fold g.

  pose (fss := min_ss u n u_has_lb).
  fold fss.

  pose (gss := min_ss u (S n) u_has_lb).
  fold gss.

  unfold glb.

  destruct (lb_to_glb f fss) as [lubf hlubf].
  destruct (lb_to_glb g gss) as [lubg hlubg].

  apply Ropp_le_contravar.

  destruct hlubf as [hubf hminf].
  destruct hlubg as [hubg hming].

  apply hming.

  unfold is_upper_bound.
  intros x hex.
  unfold EUn in hex.
  destruct hex as [nx heq].
  subst x.
  
  unfold is_upper_bound in hubf.
  apply hubf.

  unfold EUn.
  unfold opp_seq.
  unfold g.
  unfold f.
  exists (S nx).
  rewrite <- plus_n_Sm.
  rewrite plus_Sn_m.

  reflexivity.
Qed.

Lemma lub_opp_glb : forall (U:nat -> R) (hlb: has_lb U) (n:nat)
  (f:=(fun k:nat => U (n + k)%nat)),
  is_lub (EUn (opp_seq f)) (- glb f (min_ss U n hlb)).
Proof.
  intros U hlb n f.
  pose (hbf := (min_ss U n hlb)).
  fold hbf.
  unfold glb.
  destruct (lb_to_glb f hbf) as [ x0 i ].
  rewrite Ropp_involutive.
  exact i.
Qed.

Lemma Vn_Un_Wn_order :
  forall (U:nat -> R) (hub:has_ub U) (hlb:has_lb U)
    (n:nat), sequence_lb U hlb n <= U n <= sequence_ub U hub n.
Proof.
  intros U hub hlb n.

  unfold sequence_ub.
  unfold sequence_lb.

  pose (f := fun k:nat => U (n + k)%nat).
  fold f.

  pose (smin := min_ss U n hlb).
  fold f in smin.
  fold smin.

  pose (smaj := maj_ss U n hub).
  fold f in smaj.
  fold smaj.

  unfold glb.
  unfold lub.

  destruct (lb_to_glb f smin) as [ xmin imin].
  destruct (ub_to_lub f smaj) as [ xmaj imaj].

  destruct imin as [imin1 imin2].
  destruct imaj as [imaj1 imaj2].

  unfold is_upper_bound in imin1, imaj1.

  split.
  {
    apply Ropp_le_cancel.
    rewrite Ropp_involutive.
    apply imin1;clear imin1.
    unfold EUn.
    unfold opp_seq.
    unfold f.
    exists 0%nat.
    rewrite plus_comm.
    simpl.
    reflexivity.
  }
  {
    apply imaj1;clear imaj1.
    unfold EUn.
    unfold f.
    exists 0%nat.
    rewrite plus_comm.
    simpl.
    reflexivity.
  }
Qed.

Lemma min_maj :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_ub (sequence_lb Un pr2).
Proof.

  intros u hub hlb.

  unfold has_ub.
  unfold bound.

  generalize hub;intro hub'.
  unfold has_ub in hub'.
  unfold bound in hub'.
  destruct hub' as [xup hup].

  exists xup.
  unfold is_upper_bound.
  intros xn hn.

  destruct hn as [n heq].
  subst xn.

  apply Rle_trans with (u n).
  {
    apply Vn_Un_Wn_order.
    exact hub.
  }
  {
    unfold is_upper_bound in hup.
    apply hup.
    exists n.
    reflexivity.
  }
Qed.

Lemma maj_min :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_lb (sequence_ub Un pr1).
Proof.
  intros u hub hlb.
(*  assert (H := Vn_Un_Wn_order Un pr1 pr2). *)

  unfold has_lb.
  unfold bound.

  elim hlb; intros xlb hxlb.

  exists xlb.
  unfold is_upper_bound.
  intros x h.

  unfold is_upper_bound in hxlb.

  elim h; intros n heq.
  rewrite heq.

  apply Rle_trans with (opp_seq u n).
  {
    unfold opp_seq.
    apply Ropp_le_contravar.
    apply Vn_Un_Wn_order.
    exact hlb.
  }
  {
    apply hxlb.
    exists n.
    reflexivity.
  }
Qed.

Lemma cauchy_maj : forall Un:nat -> R, Cauchy_crit Un -> has_ub Un.
Proof.
  intros u h.
  unfold has_ub.
  generalize cauchy_bound;intro hcbound.
  apply cauchy_bound.
  exact h.
Qed.

Lemma cauchy_opp :
  forall Un:nat -> R, Cauchy_crit Un -> Cauchy_crit (opp_seq Un).
Proof.
  intros u h.
  unfold Cauchy_crit.
  intros e he.
  unfold Cauchy_crit in h.
  specialize (h e he).
  destruct h as [N h].
  exists N.
  intros n m hnn hnm.
  specialize (h n m hnn hnm).
  unfold R_dist in h.
  unfold R_dist.
  unfold opp_seq.
  unfold Rminus.
  rewrite <- Ropp_plus_distr.
  rewrite Rabs_Ropp.
  unfold Rminus in h.
  exact h.
Qed.

Lemma cauchy_min : forall Un:nat -> R, Cauchy_crit Un -> has_lb Un.
Proof.
  intros u h.
  unfold has_lb.
  apply cauchy_bound.
  apply cauchy_opp.
  exact h.
Qed.

Lemma maj_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    { l:R | Un_cv (sequence_ub Un (cauchy_maj Un pr)) l }.
Proof.
  intros u h.
  apply decreasing_cv.
  { apply Wn_decreasing. }
  {
    apply maj_min.
    apply cauchy_min.
    exact h.
  }
Qed.

Lemma min_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    { l:R | Un_cv (sequence_lb Un (cauchy_min Un pr)) l }.
Proof.
  intros u h.
  apply growing_cv.
  { apply Vn_growing. }
  {
    apply min_maj.
    apply cauchy_maj.
    exact h.
  }
Qed.

Lemma cond_eq_gt : forall x y:R, y < x -> (forall eps:R, 0 < eps -> Rabs (x - y) < eps) -> False.
Proof.
  intros x y hxy h.
  specialize (h (x - y)).
  apply Rlt_irrefl with (x-y).
  assert (hxy' : 0 < x - y).
  {
    unfold Rminus.
    apply Rplus_lt_reg_r with y.
    rewrite Rplus_0_l.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    exact hxy.
  }
  pattern (x-y) at 1; rewrite <- Rabs_right.
  {
    apply h.
    exact hxy'.
  }
  {
    left.
    apply Rlt_gt.
    exact hxy'.
  }
Qed.

Lemma cond_eq :
  forall x y:R, (forall eps:R, 0 < eps -> Rabs (x - y) < eps) -> x = y.
Proof.
  intros x y h.
  destruct (Req_dec x y) as [ heq | hneq ].
  { exact heq. }
  {
    apply Rdichotomy in hneq.
    destruct hneq as [ hlt | hgt ].
    {
      apply cond_eq_gt in hlt.
      { contradiction. }
      {
        intros e he.
        rewrite Rabs_minus_sym.
        apply h.
        exact he.
      }
    }
    {
      apply cond_eq_gt in hgt.
      { contradiction. }
      {
        intros e he.
        apply h.
        exact he.
      }
    }
  }
Qed.

Lemma not_Rlt : forall r1 r2:R, ~ r1 < r2 -> r1 >= r2.
Proof.
  intros x y h.
  apply Rle_ge.
  apply Rnot_gt_le.
  intro h'.
  apply h.
  apply Rgt_lt.
  exact h'.
Qed.

(* stopped here *)

Fixpoint amv u n := match n with
| O => u O
| S n' => if Rle_lt_dec (amv u n') (u n) then u n else amv u n'
end.

Arguments amv : simpl nomatch.

Fixpoint ami u n := match n with
| O => O
| S n' => if Rle_lt_dec (amv u n) (u n) then n else ami u n'
end.


Arguments ami : simpl nomatch.

Lemma amvSnl : forall u n, amv u n <= u (S n) -> amv u (S n) = u (S n).
Proof.
  intros u n.
  unfold amv.
  simpl.
  fold (amv u n).
  destruct (Rle_lt_dec (amv u n)).
  { intro h. reflexivity. }
  { intro h. exfalso. apply Rlt_irrefl with (u (S n)). destruct h as [ h | h ].
    { apply Rlt_trans with (amv u n);assumption. }
    { rewrite h in r. assumption. }
  }
Qed.

Lemma amvSnr : forall u n, u (S n) < amv u n -> amv u (S n) = amv u n.
Proof.
  intros u n.
  unfold amv.
  simpl.
  fold (amv u n).
  destruct (Rle_lt_dec (amv u n)).
  { intro h. exfalso. apply Rlt_irrefl with (u (S n)). destruct r as [ r | r ].
    { apply Rlt_trans with (amv u n);assumption. }
    { rewrite r in h. assumption. }
  }
  { intro h. reflexivity. }
Qed.

Lemma amvSn : forall u n,
  (amv u n <= u (S n) /\ amv u (S n) = u (S n)) \/
  (u (S n) < amv u n /\ amv u (S n) = amv u n).
Proof.
  intros u n.
  destruct (Rle_lt_dec (amv u n) (u (S n))).
  { left. split. assumption. rewrite amvSnl. reflexivity. assumption. }
  { right. split. assumption. rewrite amvSnr. reflexivity. assumption. }
Qed.

Lemma amiSnl : forall u n, amv u (S n) <= u (S n) -> ami u (S n) = S n.
Proof.
  intros u n h.
  unfold ami.
  fold (ami u n).
  destruct (Rle_lt_dec (amv u (S n)) (u (S n))).
  { reflexivity. }
  { exfalso. apply Rlt_irrefl with (u (S n)). destruct h as [ h | h ].
    { apply Rlt_trans with (amv u (S n));assumption. }
    { rewrite h in r. assumption. }
  }
Qed.

Lemma amiSnr : forall u n, u (S n) < amv u (S n) -> ami u (S n) = ami u n.
Proof.
  intros u n h.
  unfold ami.
  fold (ami u n).
  destruct (Rle_lt_dec (amv u (S n)) (u (S n))).
  { exfalso. apply Rlt_irrefl with (u (S n)). destruct r as [ r | r ].
    { apply Rlt_trans with (amv u (S n));assumption. }
    { rewrite r in h. assumption. }
  }
  { reflexivity. }
Qed.

Lemma amiSn : forall u n,
  (amv u (S n) <= u (S n) /\ ami u (S n) = S n) \/
  (u (S n) < amv u (S n) /\ ami u (S n) = ami u n).
Proof.
  intros u n.
  destruct (Rle_lt_dec (amv u (S n)) (u (S n))).
  { left. split. assumption. rewrite amiSnl. reflexivity. assumption. }
  { right. split. assumption. rewrite amiSnr. reflexivity. assumption. }
Qed.

Lemma VUI: forall u n, amv u n = u (ami u n).
Proof.
  induction n as [ | n i ].
  { simpl. reflexivity. }
  {
    destruct (amvSn u n) as [ [ ha eqa ] | [ ha eqa ] ].
    {
      rewrite eqa.
      destruct (amiSn u n) as [ [ hi eqi ] | [ hi eqi ] ].
      {
        rewrite eqi.
        reflexivity.
      }
      {
        exfalso. apply Rlt_irrefl with (u(S n)).
        pattern (u (S n)) at 2;rewrite <- eqa.
        assumption.
      }
    }
    {
      rewrite eqa.
      destruct (amiSn u n) as [ [ hi eqi ] | [ hi eqi ] ].
      {
        exfalso. destruct hi as [ hi | hi ].
        {
          apply Rlt_irrefl with (u (S n)).
          apply Rlt_trans with (amv u n).
          { assumption. }
          {
            rewrite eqa in hi.
            assumption.
          }
        }
        {
          apply Rlt_irrefl with (u (S n)).
          pattern (u (S n)) at 2;rewrite <- hi.
          rewrite eqa.
          exact ha.
        }
      }
      {
        rewrite i;clear i.
        rewrite eqi.
        reflexivity.
      }
    }
  }
Qed.

Lemma HubV : forall u, has_ub u -> has_ub (amv u).
Proof.
  intros u h.
  unfold has_ub in h.
  unfold bound in h.
  destruct h as [ m h ].
  unfold is_upper_bound in h.

  unfold has_ub.
  unfold bound.
  exists m.
  unfold is_upper_bound.
  intros x hn.
  destruct hn as [ n eq ].

  apply h.
  unfold EUn.

  rewrite VUI in eq.
  exists (ami u n).
  exact eq.
Qed.

Lemma HgrV : forall u, Un_growing (amv u).
Proof.
  intros u.
  unfold Un_growing.
  intro n.
  destruct n as [ | n ].
  {
    simpl.
    destruct (amvSn u 0%nat) as [ [ h eq ] | [ h eq ] ].
    { rewrite eq. simpl in h. exact h. }
    { rewrite eq. simpl. right. reflexivity. }
  }
  {
    destruct (amvSn u (S n)) as [ [ h eq ] | [ h eq ] ].
    { rewrite eq. exact h. }
    { rewrite eq. right. reflexivity. }
  }
Qed.

Lemma approx_maj :
  forall (Un:nat -> R) (pr:has_ub Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (lub Un pr - Un k) < eps.
Proof.
  intros Un pr.

  generalize pr;intro pr'.
  apply HubV in pr.
  apply ub_to_lub in pr.
  destruct pr as [ l Hl ].

  unfold lub.

  generalize pr';intro pr.
  apply ub_to_lub in pr'.
  destruct pr' as [ l' Hl' ].

  cut(l=l').
  {
    intros eq eps Heps.
    subst l'.
    destruct (Un_cv_crit_lub (amv Un) (HgrV Un) l Hl eps Heps) as (n, Hn).
    exists ((ami Un) n).
    rewrite <- VUI.
    rewrite Rabs_minus_sym.
    unfold R_dist in Hn.
    destruct (ub_to_lub Un pr).
    cut (x = l).
    {
      intro eq. subst x.
      apply Hn.
      unfold ge.
      constructor.
    }
    {
      eapply lub_unique.
      apply i.
      assumption.
    }
  }
  {
    apply Rle_antisym.
    {
      apply Hl.
      intros n (k, Hk).
      rewrite Hk, VUI.
      apply Hl'.
      now exists ((ami Un) k).
    }
    {
      apply Hl'.
      intros n (k, Hk).
      rewrite Hk.
      apply Rle_trans with ((amv Un) k).
      {
        clear.
        induction k.
        {
          apply Rle_refl.
        }
        {
          simpl.
          destruct (amvSn Un k) as [ [ h eq ] | [ h eq ] ].
          {
            rewrite eq.
            apply Rle_refl.
          }
          {
            rewrite eq.
            now apply Rlt_le.
          }
        }
      }
      {
        apply Hl.
        now exists k.
      }
    }
  }
Qed.

Lemma approx_min :
  forall (Un:nat -> R) (pr:has_lb Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (glb Un pr - Un k) < eps.
Proof.
  intros Un pr.
  unfold glb.
  destruct lb_to_glb as (lb, Hlb).
  intros eps Heps.
  destruct (approx_maj _ pr eps Heps) as (n, Hn).
  exists n.
  unfold Rminus.
  rewrite <- Ropp_plus_distr, Rabs_Ropp.
  replace lb with (lub (opp_seq Un) pr).
  { now rewrite <- (Ropp_involutive (Un n)). }
  {
    unfold lub.
    destruct ub_to_lub as (ub, Hub).
    apply Rle_antisym.
    { apply Hub. apply Hlb. }
    { apply Hlb. apply Hub. }
  }
Qed.

Lemma UL_sequence :
  forall (Un:nat -> R) (l1 l2:R), Un_cv Un l1 -> Un_cv Un l2 -> l1 = l2.
Proof.
  intros u l l' hl hl'.
  unfold Un_cv in hl, hl'.
  unfold R_dist in hl, hl'.
  apply cond_eq.
  intros eps he.
  cut (0 < eps / 2).
  {
    intro he'.
    specialize (hl (eps / 2) he').
    specialize (hl' (eps / 2) he').
    destruct hl as [N hl].
    destruct hl' as [N' hl'].
    set (M := max N N').
    apply Rle_lt_trans with (Rabs (l - u M) + Rabs (u M - l')).
    {
      replace (l - l') with (l - u M + (u M - l')).
      { apply Rabs_triang. }
      {
        unfold Rminus.
        repeat (rewrite Rplus_assoc).
        apply Rplus_eq_compat_l.
        repeat (rewrite <- Rplus_assoc).
        rewrite Rplus_opp_l.
        rewrite Rplus_0_l.
        reflexivity.
      }
    }
    {
      rewrite (double_var eps).
      apply Rplus_lt_compat.
      {
        rewrite <- Rabs_Ropp.
        rewrite Ropp_minus_distr.
        apply hl.
        unfold ge.
        unfold M.
        apply le_max_l.
      }
      {
        apply hl'.
        unfold ge.
        unfold M.
        apply le_max_r.
      }
    }
  }
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      prove_sup0.
    }
  }
Qed.

Lemma CV_plus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i + Bn i) (l1 + l2).
Proof.
  intros u v.
  intros lu lv.
  intros hu hv.
  pose (f := fun i : nat => u i + v i).
  fold f.

  unfold Un_cv in hu, hv.
  unfold Un_cv.

  intros e he.
  assert ( he' : e / 2 > 0).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      prove_sup0.
    }
  }

  specialize (hu (e / 2) he').
  specialize (hv (e / 2) he').
  clear he he'.

  destruct hu as [U hu].
  destruct hv as [V hv].

  pose (M := max U V).
  exists M.

  intros n hnM.

  unfold R_dist in hu.
  unfold R_dist in hv.
  unfold R_dist.

  unfold f;clear f.

  unfold Rminus in hu.
  unfold Rminus in hv.

  rewrite double_var.

  generalize Rabs_triang;intro a.
  specialize (a (u n + - lu) (v n + - lv)).

  apply Rle_lt_trans with (Rabs (u n + - lu) + Rabs (v n + - lv)).
  unfold Rminus.
  rewrite Ropp_plus_distr.
  replace  (u n + v n + (- lu + - lv)) with (u n + - lu + (v n + - lv)).
  { exact a. }
  {
    repeat (rewrite Rplus_assoc).
    apply Rplus_eq_compat_l.
    repeat (rewrite <- Rplus_assoc).
    apply Rplus_eq_compat_r.
    rewrite Rplus_comm.
    reflexivity.
  }
  {
    apply Rplus_lt_compat.
    {
      apply hu.
      unfold ge.
      apply le_trans with M.
      {
        unfold M.
        apply le_max_l.
      }
      {
        unfold ge in hnM.
        exact hnM.
      }
    }
    {
      apply hv.
      unfold ge.
      apply le_trans with M.
      {
        unfold M.
        apply le_max_r.
      }
      {
        unfold ge in hnM.
        exact hnM.
      }
    }
  }
Qed.

Lemma cv_cvabs :
  forall (Un:nat -> R) (l:R),
    Un_cv Un l -> Un_cv (fun i:nat => Rabs (Un i)) (Rabs l).
Proof.
  intros u l h.

  pose (f := fun i : nat => Rabs (u i)).
  fold f.

  unfold Un_cv in h.
  unfold Un_cv.

  intros e he.
  specialize (h e he).

  destruct h as [N h].
  exists N.

  intros n hn.
  specialize (h n hn).

  unfold R_dist in h.
  unfold R_dist.
  unfold f.

  apply Rle_lt_trans with (Rabs (u n - l)).
  { apply Rabs_triang_inv2. }
  { exact h. }
Qed.

Lemma CV_Cauchy :
  forall Un:nat -> R, { l:R | Un_cv Un l } -> Cauchy_crit Un.
Proof.

  intros u h.
  destruct h as [ l h ].
  unfold Cauchy_crit.
  intros e he.
  assert ( he' : e / 2 > 0).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      prove_sup0.
    }
  }
  unfold Un_cv in h.
  specialize (h _ he').
  destruct h as [ N h ].
  exists N.
  intros n m hnn hnm.
  unfold R_dist.
  unfold R_dist in h.

  replace (u n - u m) with ( (u n - l) - (u m - l)).
  2:{
    unfold Rminus.
    repeat (rewrite Rplus_assoc).
    apply Rplus_eq_compat_l.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    rewrite Rplus_comm.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    reflexivity.
  }
  {
    generalize Rabs_triang;intro a.
    eapply Rle_lt_trans.
    {
      unfold Rminus at 1.
      apply a.
    }
    {
      rewrite double_var.
      apply Rplus_lt_compat.
      {
        apply h.
        exact hnn.
      }
      {
        rewrite Rabs_Ropp.
        apply h.
        exact hnm.
      }
    }
  }
Qed.


Lemma maj_by_pos :
  forall Un:nat -> R,
    { l:R | Un_cv Un l } ->
    exists l : R, 0 < l /\ (forall n:nat, Rabs (Un n) <= l).
Proof.
  intros u h.
  destruct h as [ l h ].

  pose (f := fun k:nat => Rabs (u k)).

  assert (hf : bound (EUn f)).
  {
    apply cauchy_bound.
    apply CV_Cauchy.
    exists (Rabs l).
    apply cv_cvabs.
    exact h.
  }

  destruct hf as [ub hub].

  assert(hpos: 0 <= ub).
  {
    apply Rle_trans with (Rabs (u 0%nat)).
    { apply Rabs_pos. }
    {
      unfold is_upper_bound in hub.
      apply hub.
      exists 0%nat.
      unfold f.
      reflexivity.
    }
  }

  exists (ub + 1).

  split.
  {
    apply Rplus_le_lt_0_compat.
    exact hpos.
    exact Rlt_0_1.
  }
  {
    intros n.
    apply Rle_trans with ub.
    {
      unfold is_upper_bound in hub.
      apply hub.
      exists n.
      unfold f.
      reflexivity.
    }
    {
      pattern ub at 1; rewrite <- Rplus_0_r.
      apply Rplus_le_compat_l.
      left.
      exact Rlt_0_1.
    }
  }
Qed.

Lemma CV_mult : forall (An Bn:nat -> R) (l1 l2:R),
  Un_cv An l1 -> Un_cv Bn l2 ->
  Un_cv (fun i:nat => An i * Bn i) (l1 * l2).
Proof.

  intros u v lu lv hu hv.

  pose (f := fun i : nat => u i * v i).
  fold f.

  assert (X : { l:R | Un_cv u l }).
  {
    exists lu.
    exact hu.
  }

  apply maj_by_pos in X.
  destruct X as [ M [ hm hmaj ] ].

  unfold Un_cv.
  unfold R_dist.
  intros e he.

  assert (he' : 0 < e / (2 * M)).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat.
      { prove_sup0. }
      { exact hm. }
    }
  }

  assert (he'' : 0 < e / M).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      exact hm.
    }
  }

  assert (hmneq : M <> 0).
  {
    apply Rgt_not_eq.
    exact hm.
  }

  destruct (Req_dec lv 0) as [ hlveq | hlvneq ].
  { (* lv = 0 *)
    subst lv.

    unfold Un_cv in hv.
    unfold R_dist in hv.

    specialize (hv _ he'').
    destruct hv as [ Nv hv ].

    exists Nv.
    intros n hn.
    specialize (hv n hn).

    rewrite Rmult_0_r.
    unfold Rminus.
    rewrite Ropp_0.
    rewrite Rplus_0_r.

    unfold Rminus in hv.
    rewrite Ropp_0 in hv.
    rewrite Rplus_0_r in hv.

    unfold f.
    rewrite Rabs_mult.
    apply Rle_lt_trans with (M * Rabs (v n)).
    {
      apply Rmult_le_compat_r.
      { apply Rabs_pos. }
      { apply hmaj. }
    }
    {
      apply Rmult_lt_reg_l with (/ M).
      {
        apply Rinv_0_lt_compat.
        exact hm.
      }
      {
        rewrite <- Rmult_assoc.
        rewrite <- Rinv_l_sym.
        2:exact hmneq.
        rewrite Rmult_1_l.
        rewrite Rmult_comm.
        fold (e / M).
        exact hv.
      }
    }
  }
  {
    (* lv <> 0 *)
    assert ( hev : 0 < e / (2 * Rabs lv)).
    {
      unfold Rdiv.
      apply Rmult_lt_0_compat.
      { exact he. }
      {
        apply Rinv_0_lt_compat.
        apply Rmult_lt_0_compat.
        { prove_sup0. }
        {
          apply Rabs_pos_lt.
          exact hlvneq.
        }
      }
    }

    unfold Un_cv in hu.
    unfold R_dist in hu.
    unfold Un_cv in hv.
    unfold R_dist in  hv.
    specialize (hu _ hev).
    destruct hu as [ Nu hu ].
    specialize (hv _ he').
    destruct hv as [ Nv hv ].
    set (N := max Nu Nv).
    exists N.
    intros n hn.

    pattern (f n); rewrite <- Rplus_0_r.
    unfold f.
    unfold Rminus.
    rewrite <- Rplus_opp_l with (u n * lv).
    repeat (rewrite Rplus_assoc).
    rewrite <- Rplus_assoc.

    eapply Rle_lt_trans.
    1:apply Rabs_triang.

    rewrite Ropp_mult_distr_r.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rabs_mult.
    fold (v n - lv).

    rewrite Ropp_mult_distr_l.
    rewrite <- Rmult_plus_distr_r.
    rewrite Rabs_mult.
    fold (u n - lu).

    rewrite (double_var e).
    apply Rplus_lt_compat.
    {
      apply Rle_lt_trans with (M * Rabs (v n - lv)).
      {
        apply Rmult_le_compat_r.
        { apply Rabs_pos. }
        { apply hmaj. }
      }
      {
        apply Rmult_lt_reg_l with (/ M).
        {
          apply Rinv_0_lt_compat.
          apply hm.
        }
        {
          rewrite <- Rmult_assoc.
          rewrite <- Rinv_l_sym.
          2:exact hmneq.
          rewrite Rmult_1_l.
          rewrite Rmult_comm.
          unfold Rdiv.
          rewrite Rmult_assoc.
          rewrite <- Rinv_mult_distr.
          2:discrR.
          2:exact hmneq.
          apply hv.
          unfold ge.
          apply le_trans with N.
          {
            unfold N.
            apply le_max_r.
          }
          { exact hn. }
        }
      }
    }
    {
      apply Rmult_lt_reg_l with (/ Rabs lv).
      {
        apply Rinv_0_lt_compat.
        apply Rabs_pos_lt.
        exact hlvneq.
      }
      {
        rewrite (Rmult_comm _ (Rabs lv)).
        rewrite <- Rmult_assoc.
        rewrite <- Rinv_l_sym.
        2:{
          apply Rabs_no_R0.
          exact hlvneq.
        }
        {
          rewrite Rmult_1_l.
          rewrite (Rmult_comm (/ Rabs lv)).
          unfold Rdiv.
          rewrite Rmult_assoc.
          rewrite <- Rinv_mult_distr.
          2:discrR.
          2:apply Rabs_no_R0;exact hlvneq.
          apply hu.
          unfold ge.
          apply le_trans with N.
          {
            unfold N.
            apply le_max_l.
          }
          {
            unfold ge in hn.
            exact hn.
          }
        }
      }
    }
  }
Qed.

Lemma tech9 : forall Un:nat -> R,
    Un_growing Un -> forall m n:nat, (m <= n)%nat -> Un m <= Un n.
Proof.
  intros u hg n m h.
  apply Rge_le.
  apply growing_prop.
  { exact hg. }
  { unfold ge. exact h. }
Qed.

Lemma tech13 : forall (An:nat -> R) (k:R)
  ( f := fun n : nat => Rabs (An (S n) / An n)),
  0 <= k < 1 ->
  Un_cv f k ->
  exists k0 : R,
    k < k0 < 1 /\
    (exists N : nat,
      (forall n:nat, (N <= n)%nat -> f n < k0)).
Proof.
  intros u k f hk hu.
  exists (k + (1 - k) / 2).
  split.
  {
    split.
    {
      pattern k at 1; rewrite <- Rplus_0_r.
      apply Rplus_lt_compat_l.
      unfold Rdiv.
      apply Rmult_lt_0_compat.
      2:apply Rinv_0_lt_compat; prove_sup0.
      apply Rplus_lt_reg_l with k.
      rewrite Rplus_0_r.
      unfold Rminus.
      rewrite (Rplus_comm 1).
      rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_l.
      apply hk.
    }
    {
      apply Rmult_lt_reg_l with 2.
      1:prove_sup0.
      unfold Rdiv.
      rewrite Rmult_1_r.
      rewrite Rmult_plus_distr_l.
      pattern 2 at 1; rewrite Rmult_comm.
      rewrite Rmult_assoc.
      rewrite <- Rinv_l_sym.
      2:discrR.
      rewrite Rmult_1_r.
      unfold Rminus.
      rewrite (Rplus_comm 1).
      rewrite <- Rplus_assoc.
      pattern (-k);rewrite <- Rmult_1_l.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l.
      rewrite <- Rmult_plus_distr_r.
      unfold IZR at 1.
      unfold IPR, IPR_2.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_r.
      rewrite Rmult_1_l.
      rewrite Rplus_comm.
      apply Rplus_lt_compat_l.
      apply hk.
    }
  }
  {
    unfold Un_cv in hu.
    assert (he : (0 < (1 - k) / 2)).
    {
      unfold Rdiv.
      apply Rmult_lt_0_compat.
      2:apply Rinv_0_lt_compat; prove_sup0.
      apply Rplus_lt_reg_l with k.
      rewrite Rplus_0_r.
      unfold Rminus.
      rewrite Rplus_comm.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_r.
      apply hk.
    }
    {
      specialize (hu _ he).
      destruct hu as [ N hu ].
      exists N.
      intros n hnn.
      specialize (hu n hnn).
      unfold R_dist in hu.
      unfold f.
      rewrite <- Rabs_Rabsolu.
      replace (Rabs (u (S n) / u n)) with (Rabs (u (S n) / u n) - k + k).
      2:{
        unfold Rminus.
        rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        reflexivity.
      }
      eapply Rle_lt_trans.
      1:apply Rabs_triang.
      rewrite (Rabs_right k).
      2:apply Rle_ge;apply hk.
      apply Rplus_lt_reg_l with (- k).
      rewrite <- (Rplus_comm k).
      repeat rewrite <- Rplus_assoc.
      rewrite Rplus_opp_l.
      repeat rewrite Rplus_0_l.
      unfold f in hu.
      exact hu.
    }
  }
Qed.

Lemma growing_ineq : forall (Un:nat -> R) (l:R),
  Un_growing Un -> Un_cv Un l -> forall n:nat, Un n <= l.
Proof.
  intros u l hg hu n.
  destruct (total_order_T (u n) l) as [[ ho | ho ] | ho ].
  { left. exact ho. }
  { right. exact ho. }
  {
    unfold Un_cv in hu.
    unfold R_dist in hu.
    assert (he: 0 < u n - l).
    {
      apply Rplus_lt_reg_r with l.
      rewrite Rplus_0_l.
      unfold Rminus.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_r.
      exact ho.
    }

    specialize (hu _ he); clear he.
    destruct hu as [ N hu ].

    exfalso.
    set (M := max n N).

    assert (growing_side : u n - l <= u M - l).
    {
      unfold Rminus.
      apply Rplus_le_compat_r.
      apply Rge_le.
      apply growing_prop.
      { exact hg. }
      {
        unfold ge.
        unfold M.
        apply le_max_l.
      }
    }

    assert (cv_side : u M - l < u n - l).
    {
      apply Rle_lt_trans with (Rabs (u M - l)).
      { apply RRle_abs. }
      {
        apply hu.
        unfold ge.
        unfold M.
        apply le_max_r.
      }
    }

    eapply Rlt_irrefl.
    eapply Rle_lt_trans.
    1:apply growing_side.
    exact cv_side.
  }
Qed.

(** Un->l => (-Un) -> (-l) *)
Lemma CV_opp : forall (An:nat -> R) (l:R),
  Un_cv An l -> Un_cv (opp_seq An) (- l).
Proof.
  intros u l h.
  unfold Un_cv.
  intros e he.
  unfold Un_cv in h.
  specialize (h e he).
  destruct h as [ N h ].
  exists N.
  intros n hnn.
  specialize (h n hnn).
  unfold opp_seq.
  unfold R_dist.
  unfold R_dist in h.
  unfold Rminus.
  rewrite <- Ropp_plus_distr.
  rewrite Rabs_Ropp.
  exact h.
Qed.

Lemma decreasing_ineq : forall (Un:nat -> R) (l:R),
    Un_decreasing Un -> Un_cv Un l -> forall n:nat, l <= Un n.
Proof.
  intros u l hd hl n.
  generalize decreasing_growing;intro hg.
  specialize (hg u hd).
  generalize CV_opp;intro hopp.
  specialize (hopp u l hl).
  generalize growing_ineq; intro gi.
  specialize (gi (opp_seq u) (-l) hg hopp n).
  unfold opp_seq in gi.
  apply Ropp_le_cancel.
  exact gi.
Qed.

Lemma CV_minus : forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i - Bn i) (l1 - l2).
Proof.
  intros An Bn l1 l2 H H0.
  replace (fun i:nat => An i - Bn i) with (fun i:nat => An i + opp_seq Bn i).
  {
    unfold Rminus.
    apply CV_plus.
    { exact H. }
    {
      apply CV_opp.
      exact H0.
    }
  }
  {
    unfold Rminus.
    unfold opp_seq.
    reflexivity.
  }
Qed.

Definition cv_infty (Un:nat -> R) : Prop :=
  forall M:R,  exists N : nat, (forall n:nat, (N <= n)%nat -> M < Un n).

Lemma cv_infty_cv_R0 : forall Un:nat -> R,
    (forall n:nat, Un n <> 0) ->
    cv_infty Un ->
    Un_cv (fun n:nat => / Un n) 0.
Proof.

  intros u hneq hinf.
  pose (f := fun n : nat => / u n).
  fold f.

  unfold cv_infty in hinf.
  unfold Un_cv.
  intros e he.
  specialize (hinf (/ e)).
  destruct hinf as [ N hinf ].
  exists N.
  intros n hnn.
  unfold ge in hnn.
  specialize (hinf n hnn).
  unfold R_dist.
  unfold Rminus.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  unfold f.
  rewrite Rabs_Rinv.
  2:apply hneq.
  apply Rmult_lt_reg_r with (Rabs (u n)).
  1:{
    apply Rabs_pos_lt.
    apply hneq.
  }
  rewrite Rinv_l.
  2:{
    apply Rgt_not_eq.
    apply Rabs_pos_lt.
    apply hneq.
  }
  apply Rmult_lt_reg_l with (/ e).
  1:{
    apply Rinv_0_lt_compat.
    exact he.
  }
  rewrite Rmult_1_r.
  rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  2:{
    apply Rgt_not_eq.
    exact he.
  }
  rewrite Rmult_1_l.
  apply Rlt_le_trans with (u n).
  exact hinf.
  apply RRle_abs.
Qed.

Lemma decreasing_prop : forall (Un:nat -> R) (m n:nat),
    Un_decreasing Un -> (m <= n)%nat -> Un n <= Un m.
Proof.
  intros u m n hu hmn.
  unfold Un_decreasing in hu.
  induction n as [ | n ni ].
  {
    induction m as [ | m mi ].
    {
      right.
      reflexivity.
    }
    { inversion hmn. }
  }
  {
    assert (disj : (m <= n)%nat \/ m = S n).
    {
      inversion hmn as [ hmn' | n' hmn' n'eq ].
      {
        right.
        reflexivity.
      }
      {
        subst n'.
        left.
        exact hmn'.
      }
    }
    {
      destruct disj as [ hmn' | hmn' ].
      {
        apply Rle_trans with (u n).
        { apply hu. }
        {
          apply ni.
          exact hmn'.
        }
      }
      {
        subst m.
        right.
        reflexivity.
      }
    }
  }
Qed.

Definition pow_fact x n := x ^ n / INR (fact n).

Definition pow_fact_abs x n := Rabs x ^ n / INR (fact n).

Lemma cv_pfa_pf : forall x, Un_cv (pow_fact_abs x) 0 -> Un_cv (pow_fact x) 0.
Proof.
  intros x h.

  unfold Un_cv.
  intros e he.

  unfold Un_cv in h.
  specialize (h _ he).
  destruct h as [ N h ].

  exists N.

  intros n hn.
  specialize (h n hn).

  unfold R_dist.
  unfold R_dist in h.

  unfold Rminus.
  rewrite Ropp_0.
  rewrite Rplus_0_r.

  unfold Rminus in h.
  rewrite Ropp_0 in h.
  rewrite Rplus_0_r in h.

  unfold pow_fact.
  unfold pow_fact_abs in h.

  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite <- Rabs_Rabsolu.
  rewrite <- RPow_abs.
  rewrite <- Rabs_mult.

  exact h.
Qed.

Definition pow_fact_abs_mn x M n := Rabs x ^ (M + n) / INR (fact (M + n)).

Definition fsn n := INR (S n).

Lemma cv_fsn : cv_infty fsn.
Proof.
  unfold cv_infty.
  intro M.
  destruct (total_order_T M 0) as [ [ hM | hM ] | hM ].
  {
    exists 0%nat.
    intros n hn.
    apply Rlt_trans with 0.
    { exact hM. }
    {
      unfold fsn.
      apply lt_INR_0.
      apply lt_O_Sn.
    }
  }
  {
    subst M.
    exists 0%nat.
    intros n hn.
    unfold fsn.
    apply lt_INR_0.
    apply lt_O_Sn.
  }
  {
    set (Mz := up M).
    assert (Hmz : (0 <= Mz)%Z).
    {
      apply le_IZR.
      left.
      unfold Mz.
      apply Rlt_trans with M.
      { exact hM. }
      { apply archimed. }
    }
    apply IZN in Hmz.
    destruct Hmz as [ Mn hMeq ].
    exists Mn.
    intros n hn.
    apply Rlt_le_trans with (IZR Mz).
    { apply archimed. }
    {
      rewrite hMeq.
      rewrite <- INR_IZR_INZ.
      unfold fsn.
      apply le_INR.
      apply le_trans with n.
      { exact hn. }
      { apply le_n_Sn. }
    }
  }
Qed.

Definition fsn_inv n := / INR (S n).

Lemma cv_fsn_inv : Un_cv fsn_inv 0.
Proof.
  apply cv_infty_cv_R0.
  {
    intro n.
    apply not_O_INR.
    intro eq.
    inversion eq.
  }
  {
    fold fsn.
    exact cv_fsn.
  }
Qed.

Lemma pow_fact_abs_mn_pos : forall x M n,
  0 < Rabs x -> 0 < pow_fact_abs_mn x M n.
Proof.
  intros x M n h.
  unfold pow_fact_abs_mn.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  {
    apply pow_lt.
    exact h.
  }
  {
    apply Rinv_0_lt_compat.
    apply lt_INR_0.
    apply lt_O_fact.
  }
Qed.

Lemma cv_pow_fact_abs_mn : forall x M,
  x <> 0 ->
  up (Rabs x) = Z.of_nat M ->
  Un_cv (pow_fact_abs_mn x M) 0.
Proof.
  intros x M hx hM.
  assert (hxa := Rabs_pos_lt x hx).
  unfold Un_cv.
  unfold R_dist.
  intros e he.
  set (Un := pow_fact_abs_mn x M).
  set (Vn := fun n:nat => Rabs x * (Un 0%nat / INR (S n))).

  assert (H6 : (1 <= M)%nat).
  {
    clear - hM hxa.
    apply INR_le.
    simpl.
    destruct M as [ | M ].
    {
      exfalso.
      destruct (archimed (Rabs x)) as [ H7 H8 ].
      rewrite hM in H7.
      rewrite <- INR_IZR_INZ in H7.
      simpl in H7.
      eapply Rlt_irrefl.
      eapply Rlt_trans.
      { exact hxa. }
      { exact H7. }
    }
    {
      apply (le_INR 1).
      apply le_n_S.
      apply le_O_n.
    }
  }



  assert (H8 : Un_decreasing Un).
  {
    unfold Un.
    clear - hxa hM.
    unfold Un_decreasing.
    intro n.
    unfold pow_fact_abs_mn.
    fold (1+n)%nat.
    rewrite (plus_comm 1 n).
    rewrite plus_assoc.
    rewrite pow_add.
    unfold Rdiv.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    {
      left.
      apply pow_lt.
      exact hxa.
    }
    {
      simpl.
      rewrite Rmult_1_r.
      rewrite <- plus_assoc.
      rewrite (plus_comm n).
      simpl.
      rewrite <- plus_n_Sm.
      apply Rmult_le_reg_l with (INR (fact (S (M + n)))).
      {
        apply lt_INR_0.
        apply neq_O_lt.
        intro H8.
        eapply fact_neq_0.
        rewrite H8.
        reflexivity.
      }
      {
        rewrite (Rmult_comm (Rabs x)).
        rewrite <- Rmult_assoc.
        rewrite <- Rinv_r_sym.
        {
          rewrite Rmult_1_l.
          rewrite fact_simpl.
          rewrite mult_INR.
          rewrite Rmult_assoc.
          rewrite <- Rinv_r_sym.
          {
            rewrite Rmult_1_r.
            apply Rle_trans with (INR M).
            {
              left.
              rewrite INR_IZR_INZ.
              rewrite <- hM.
              apply archimed.
            }
            {
              apply le_INR.
              apply le_trans with (S M).
              { apply le_n_Sn. }
              {
                rewrite <- plus_Sn_m.
                apply le_plus_l.
              }
            }
          }
          { apply INR_fact_neq_0. }
        }
        { apply INR_fact_neq_0. }
      }
    }
  }


  assert (H9 : forall n:nat, Un (S n) <= Vn n).
  {
    intro n.
    apply Rle_trans with (Rabs x * Un n * / INR (S n)).
    {
      unfold Un.
      unfold pow_fact_abs_mn.
      fold (plus 1 n).
      rewrite (plus_comm 1 n).
      rewrite plus_assoc.
      rewrite pow_add.
      simpl pow.
      rewrite Rmult_1_r.
      unfold Rdiv.
      rewrite <- (Rmult_comm (Rabs x)).
      repeat rewrite Rmult_assoc.
      apply Rmult_le_compat_l.
      { apply Rabs_pos. }
      {
        apply Rmult_le_compat_l.
        {
          left.
          apply pow_lt.
          exact hxa.
        }
        {
          rewrite <- plus_assoc.
          rewrite (plus_comm n).
          simpl plus.
          rewrite <- plus_n_Sm.
          rewrite fact_simpl.
          rewrite mult_comm.
          rewrite mult_INR.
          rewrite Rinv_mult_distr.
          {
            apply Rmult_le_compat_l.
            {
              left.
              apply Rinv_0_lt_compat.
              apply lt_INR_0.
              apply neq_O_lt.
              intro eq.
              eapply fact_neq_0.
              rewrite eq.
              reflexivity.
            }
            {
              left.
              apply Rinv_lt_contravar.
              {
                apply Rmult_lt_0_compat.
                {
                  apply lt_INR_0.
                  apply lt_O_Sn.
                } 
                {
                  apply lt_INR_0.
                  apply lt_O_Sn.
                } 
              }
              {
                apply lt_INR.
                apply lt_n_S.
                apply Nat.lt_add_pos_l.
                unfold lt.
                exact H6.
              }
            }
          }
          { apply INR_fact_neq_0. }
          {
            apply not_O_INR.
            intro eq.
            inversion eq.
          }
        }
      }
    }
    {
      unfold Vn.
      rewrite Rmult_assoc.
      unfold Rdiv.
      rewrite (Rmult_comm (Un 0%nat)).
      rewrite (Rmult_comm (Un n)).
      repeat apply Rmult_le_compat_l.
      { apply Rabs_pos. }
      {
        left.
        apply Rinv_0_lt_compat.
        apply lt_INR_0.
        apply lt_O_Sn.
      }
      {
        apply decreasing_prop.
        { exact H8. }
        { apply le_O_n. }
      }
    }
  }





  assert (H10: Un_cv Vn 0).
  {



                unfold Un_cv.
                intros eps1 H12.
                unfold R_dist.
                unfold Vn.
                generalize cv_fsn_inv;intro Htata.
                unfold Un_cv in Htata.
                unfold R_dist in Htata.
                assert ( H13 : 0 < eps1 / (Rabs x * Un 0%nat)).
                {
                  unfold Rdiv.
                  apply Rmult_lt_0_compat.
                  { exact H12. }
                  {
                    apply Rinv_0_lt_compat.
                    apply Rmult_lt_0_compat.
                    {
                      apply Rabs_pos_lt.
                      exact hx.
                    }
                    {
                      unfold Un.
                      apply pow_fact_abs_mn_pos.
                      exact hxa.
                    }
                  }
                }

                  specialize (Htata _ H13).
                  destruct Htata as [ N H14 ].
                  exists N.
                  intros n H15.
                  replace (Rabs x * (Un 0%nat / INR (S n)) - 0) with  (Rabs x * Un 0%nat * (/ INR (S n) - 0)).
                  2:{
                    unfold Rdiv.
                    unfold Rminus.
                    rewrite Ropp_0.
                    rewrite Rplus_0_r.
                    rewrite Rplus_0_r.
                    rewrite Rmult_assoc.
                    reflexivity.
                  }
                  rewrite Rabs_mult.
                  apply Rmult_lt_reg_l with (/ Rabs (Rabs x * Un 0%nat)).
                  {
                    apply Rinv_0_lt_compat.
                    apply Rabs_pos_lt.
                    apply prod_neq_R0.
                    {
                      apply Rabs_no_R0.
                      exact hx.
                    }
                    {
                      intro eq.
                      apply Rlt_irrefl with 0.
                      pattern 0 at 2;rewrite <- eq.
                      unfold Un.
                      apply pow_fact_abs_mn_pos.
                      exact hxa.
                    }
                  }
                  {
                    rewrite <- Rmult_assoc.
                    rewrite <- Rinv_l_sym.
                    {
                      rewrite Rmult_1_l.
                      replace (/ Rabs (Rabs x * Un 0%nat) * eps1) with (eps1 / (Rabs x * Un 0%nat)).
                      {
                        apply H14.
                        exact H15.
                      }
                      {
                        unfold Rdiv.
                        rewrite (Rabs_right (Rabs x * Un 0%nat)).
                        { apply Rmult_comm. }
                        {
                          apply Rle_ge.
                          apply Rmult_le_pos.
                          { apply Rabs_pos. }
                          {
                            left.
                            unfold Un.
                            apply pow_fact_abs_mn_pos.
                            exact hxa.
                          }
                        }
                      }
                    }
                    {
                      apply Rabs_no_R0.
                      apply prod_neq_R0.
                      {
                        apply Rabs_no_R0.
                        exact hx.
                      }
                      {
                        intro eq.
                        apply Rlt_irrefl with 0.
                        pattern 0 at 2;rewrite <- eq.
                        unfold Un.
                        apply pow_fact_abs_mn_pos.
                        exact hxa.
                      }
                    }
                  }
                }




            


            unfold Un_cv in H10.
            unfold R_dist in H10.
            specialize (H10 _ he).
            destruct H10 as [ N1 H11 ].
            exists (S N1).
            intros n H12.
            cut (forall n:nat, 0 < Vn n).
            {
              intro H13.
              apply Rle_lt_trans with (Rabs (Vn (pred n) - 0)).
              {
                rewrite Rabs_right.
                {
                  rewrite Rabs_right.
                  {
                    unfold Rminus.
                    rewrite Ropp_0.
                    rewrite Rplus_0_r.
                    rewrite Rplus_0_r.
                    replace n with (S (pred n)).
                    { apply H9. }
                    {
                      inversion H12.
                      {
                        simpl.
                        reflexivity.
                      }
                      {
                        simpl.
                        reflexivity.
                      }
                    }
                  }
                  {
                    apply Rle_ge.
                    unfold Rminus.
                    rewrite Ropp_0.
                    rewrite Rplus_0_r.
                    left.
                    apply H13.
                  }
                }
                {
                  apply Rle_ge.
                  unfold Rminus.
                  rewrite Ropp_0.
                  rewrite Rplus_0_r.
                  left.
                  unfold Un.
                  apply pow_fact_abs_mn_pos.
                  exact hxa.
                }
              }
              {
                apply H11.
                unfold ge.
                apply le_S_n.
                replace (S (pred n)) with n.
                {
                  unfold ge in H12.
                  exact H12.
                }
                {
                  inversion H12.
                  {
                    simpl.
                   reflexivity.
                  }
                  {
                    simpl.
                   reflexivity.
                  }
                }
              }
            }
            {
              intro n0.
              apply Rlt_le_trans with (Un (S n0)).
              {
                unfold Un.
                apply pow_fact_abs_mn_pos.
                exact hxa.
              }
              { apply H9. }
            }
Qed.

Lemma cv_speed_pow_fact : forall (x:R),
  Un_cv (pow_fact x) 0.
Proof.
  intros x.
  apply cv_pfa_pf.
  unfold Un_cv.
  intros e he.
  unfold R_dist.

  destruct (Req_dec x 0) as [ hx | hx ].
  {
    subst x.
    unfold pow_fact_abs.
    exists 1%nat.
    intros n hn.
    unfold Rminus.
    rewrite Ropp_0.
    rewrite Rplus_0_r.
    rewrite Rabs_R0.
    rewrite pow_ne_zero.
    {
      unfold Rdiv.
      rewrite Rmult_0_l.
      rewrite Rabs_R0.
      exact he.
    }
    {
      intro eq.
      subst n.
      unfold ge in hn.
      inversion hn.
    }
  }
  {
    assert (hxa := Rabs_pos_lt x hx).
    set (Mz := up (Rabs x)).

    assert (hM: (0 <= Mz)%Z).
    {
      clear - hxa.
      unfold Mz.
      apply le_IZR.
      left.
      apply Rlt_trans with (Rabs x).
      { exact hxa. }
      { apply archimed. }
    }

    apply IZN in hM.
    destruct hM as [ M hM ].
    subst Mz.

    set (Un := pow_fact_abs_mn x M).
    generalize cv_pow_fact_abs_mn; intro h.
    specialize (h x M hx hM).
    fold Un in h.

    unfold Un_cv in h.
    specialize (h _ he).
    destruct h as [ N h ].
    exists (M + N)%nat.
    intros n hn.

    unfold R_dist in h.

    assert (hex : exists p : nat, (p >= N)%nat /\ n = (M + p)%nat).
    {
      exists (n - M)%nat.
      split.
      {
        unfold ge.
        apply (plus_le_reg_l _ _ M).
        rewrite <- le_plus_minus.
        { exact hn. }
        {
          apply le_trans with (M + N)%nat.
          { apply le_plus_l. }
          { exact hn. }
        }
      }
      {
        apply le_plus_minus.
        apply le_trans with (M + N)%nat.
        { apply le_plus_l. }
        { exact hn. }
      }
    }

    destruct hex as [ p [ hp heq ] ].
    subst n.
    unfold Un in h.
    unfold pow_fact_abs_mn in h.
    unfold pow_fact_abs.
    apply h.
    exact hp.
  }
Qed.
