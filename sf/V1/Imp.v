Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Maps.
Require Import Coq.Logic.FunctionalExtensionality.
Import Setoid.

Module MSkip.

Definition state := total_map nat.

Inductive com : Type :=
| CSkip : com
.

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall s:state, ceval CSkip s s
.

Theorem ceval_deterministic : forall (c:com) (src:state) (dst1:state) (dst2:state),
ceval c src dst1 -> ceval c src dst2 -> dst1 = dst2.
intros c src dst1 dst2.
intros h1 h2.
inversion h1. subst s. subst dst1.
subst c.
inversion h2. subst s. subst dst2.
reflexivity.
Qed.

Theorem nothing: forall (c:com) (src dst:state),
ceval c src dst -> src = dst.
intros c src dst.
intro h. inversion h. reflexivity.
Qed.

End MSkip.

Module MAssignment.

Definition state := partial_map nat.

Inductive com : Type :=
| CSkip : com
| CAss : string -> nat -> com
.

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall s:state, ceval CSkip s s
| E_Ass : forall (s:state) (id:string) (n:nat), ceval (CAss id n) s (update s id n)
.

Theorem alln : forall (n:nat) (src dst:state), exists (c:com), ceval c src dst -> exists id:string, dst id = Some n.
intros n src dst.
exists (CAss "A" n).
intro h.
exists "A"%string.
inversion h. subst n0. subst id. subst s.
unfold update.
unfold t_update.
rewrite beq_string_refl.
reflexivity.
Qed.

Theorem state_different_single_variable : forall (src dst:state) (c:com),
src=empty /\ ceval c src dst /\ src <> dst ->
exists (id:string) (n:nat), dst id = Some n /\
  forall (id':string) (n':nat), dst id' = Some n' -> n=n' /\ id=id'.
Proof.
intros src dst c.
intros [empty [heval hneq]].
inversion heval.
subst c. subst s. subst src. contradiction.
subst s. exists id. exists n.
split.
unfold update. unfold t_update. rewrite beq_string_refl. reflexivity.
intros id' n'.
intro update'.
unfold update in update'.
unfold t_update in update'.
subst c.

unfold beq_string in update'.
destruct (string_dec id id').
subst id'.
inversion update'.
subst n'.
split;reflexivity.

subst src. inversion update'.

Qed.


End MAssignment.

Module MSkipAndSeq.

Definition state := partial_map nat.

Inductive com : Type :=
| CSkip : com
| CSeq : com -> com -> com
.

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall s:state, ceval CSkip s s
| E_Seq : forall (src tmp dst:state) (c1 c2:com), ceval c1 src tmp -> ceval c2 tmp dst -> ceval (CSeq c1 c2) src dst
.

Theorem nothing : forall (src dst:state) (c:com), ceval c src dst -> src = dst.
Proof.
intros src dst c.
generalize src dst.
clear src dst.
induction c.
intros src dst heval. inversion heval. reflexivity.
intros src dst heval.
inversion heval.
subst dst0 src0 c3 c0.
rewrite <- (IHc2 tmp dst).
rewrite <- (IHc1 src tmp).
reflexivity. assumption. assumption.
Qed.

Theorem nothing2 : forall (s:state) (c:com), ceval c s s.
Proof.
intros s c. generalize s. clear s. induction c.
intros;constructor.
intro s.
apply (E_Seq s s s). apply IHc1. apply IHc2.
Qed.

Theorem something_impossible : forall (src dst:state) (c:com), not (ceval c src dst /\ src <> dst).
intros src dst c.
intros [heval hneq].
apply hneq.
rewrite (nothing src dst c). reflexivity. assumption.
Qed.

Fixpoint contains_skip (c:com) : Prop :=
match c with
| CSkip => True
| CSeq c1 c2 => (contains_skip c1) \/ (contains_skip c2)
end.

Theorem must_skip : forall (src dst:state) (c:com), ceval c src dst -> contains_skip c.
intros src dst c.
generalize dependent dst.
generalize dependent src.
induction c.
simpl. trivial.
intros src dst heval.
simpl.
inversion heval.
subst dst0 src0 c3 c0.
right. apply (IHc2 tmp dst). assumption.
Qed.

Fixpoint depth (c:com) : nat :=
match c with
| CSkip => 0
| CSeq c1 c2 => S (max (depth c1) (depth c2))
end.

Theorem any_depth : forall (s:state) (n:nat), exists c:com, depth c = n /\ ceval c s s.
intros s n.
generalize dependent s.
induction n.
intro s. exists CSkip. simpl. split. reflexivity. constructor.
intro s.
specialize (IHn s).
inversion_clear IHn as [c' [hdepth heval]].
exists (CSeq c' c').
simpl.
rewrite Nat.max_id.
rewrite hdepth. split. reflexivity. apply (E_Seq s s s). assumption. assumption.
Qed.

Theorem depth_0_Skip : forall (s:state) (c:com), depth c = 0 -> ceval c s s -> c = CSkip.
intros s c hdepth heval.
destruct c. reflexivity.
simpl in hdepth. inversion hdepth.
Qed.

Fixpoint count_skip (c:com) : nat :=
match c with
| CSkip => 1
| CSeq c1 c2 => (count_skip c1) + (count_skip c2)
end.

Search "even".

Theorem nm0 : forall (n m:nat), n+m=0->n=0/\m=0.
intro n. induction n.
destruct m. simpl. intro;split;reflexivity.
simpl. intro h;inversion h.
intro m. simpl. intro h. inversion h.
Qed.

Theorem nm1 : forall (n m :nat), n+m=1->n=1\/m=1.
intro n. induction n.
simpl. intros m h. right. assumption.
simpl.
intros m h. inversion h. apply nm0 in H0.
inversion_clear H0 as [n0 m0].
subst m. subst n.
simpl. left. reflexivity. 
Qed.

Theorem count_skip_nonzero : forall (src dst:state) (c:com), ceval c src dst -> count_skip c <> 0.
intros src dst.
intro c.
generalize dependent dst.
generalize dependent src.
induction c.
simpl. intros. intro impossible. inversion impossible.
intros src dst.
intro heval.
intro hcs.
inversion heval.
subst dst0. subst src0. subst c3. subst c0.
simpl in hcs.
apply nm0 in hcs. inversion_clear hcs as [h1 h2].
apply (IHc2 tmp dst). assumption. assumption.
Qed.

Fixpoint count_all (c:com) : nat :=
match c with
| CSkip => 1
| CSeq c1 c2 => 1 + count_all(c1) + count_all(c2)
end.



Theorem no2 : forall (c:com), count_all c <> 2.
Proof.
intros c.
induction c.
simpl. intros. trivial.
intros.
destruct c1;destruct c2.
simpl. auto.
simpl. intro h. inversion h.
simpl. intro h. inversion h.

simpl in IHc1.

apply nm0 in H0. inversion H0. inversion H1.

simpl. intro h.
inversion h. clear h.
apply nm0 in H0. inversion_clear H0.
inversion H1.
Qed.

Fixpoint count_seq (c:com) : nat :=
match c with
| CSkip => 0
| CSeq x y => 1 + (count_seq x) + (count_seq y)
end.


Theorem nGt0_npnGt1 : forall n:nat, n>0 -> n+n>1.
intros n h.
destruct h. auto. simpl. rewrite plus_comm. simpl.
clear h.
induction m. auto. simpl. rewrite plus_comm. simpl.
apply (gt_trans _ (S(S(m+m))) _).
auto. assumption.
Qed.

Theorem nmGtOnpmGt1 : forall (n m:nat), n>0 -> m>0 -> n+m>1.
unfold gt. unfold lt.
intros n m hn hm.
induction hn. simpl.
Search ( _ <= _ -> _ <= _).
apply le_n_S. assumption.
rename m0 into n. destruct hm. simpl. apply (le_trans _ (n+1) _). assumption. auto.
apply (le_trans _ (n + S m) _). assumption.
simpl. rewrite plus_comm at 2. simpl. rewrite plus_comm at 1. simpl. auto.
Qed.

Theorem more_skip_helper : forall (n m o p : nat), n > S o -> m > S p -> n + m > S(S o + S p).
unfold gt. unfold lt.
intros n m o p.
intros hon.
induction hon. simpl. intros.
Search (_ <= _ -> S _ <= S _).
apply le_n_S. apply le_n_S.
rewrite plus_n_Sm.
Search ( _ <= _ -> _ + _ <= _ + _ ).
apply plus_le_compat_l. assumption.
simpl. intros.
rename m0 into q.
simpl in IHhon.
apply (le_trans _ (q+m) _).
apply IHhon. assumption.
rewrite plus_n_Sm.
apply plus_le_compat_l. auto.
Qed.


Theorem more_skip : forall (c:com), count_skip c > count_seq c.
induction c.
simpl. auto.
simpl.
destruct c1;destruct c2.
simpl. auto.
simpl. simpl in IHc1. simpl in IHc2.
rename c2_1 into a. rename c2_2 into b.
Search (_ > _ -> S _ > S _). apply gt_n_S. assumption.
simpl. simpl in IHc1. simpl in IHc2.
rewrite plus_comm at 1. simpl. apply gt_n_S.
Search ( _ + 0).
rewrite <- plus_n_O. assumption.
rename c1_1 into a. rename c1_2 into b. rename c2_1 into c. rename c2_2 into d.
simpl in IHc1. simpl in IHc2.
simpl.
apply more_skip_helper. assumption. assumption.
Qed.

Theorem any_skip : forall (n:nat), n<>0 -> exists (c:com), count_skip c = n.
destruct n. intro h. contradiction.
intro h. clear h.
induction n. exists CSkip. simpl. reflexivity.
inversion IHn.
exists (CSeq CSkip x ).
simpl. rewrite H. reflexivity.
Qed.

Theorem any_seq : forall (n:nat), exists (c:com), count_seq c = n.
induction n. exists CSkip. simpl. reflexivity.
inversion IHn. exists (CSeq CSkip x). simpl. rewrite H. reflexivity.
Qed.

Theorem all1orgt2_helper : forall n m o : nat, o <= n -> o <= m -> o <= n + m.
intros n m o hon .
induction hon.
intro.
apply (le_trans _ m _). assumption.
rewrite plus_comm.
rewrite plus_n_O at 1.
apply plus_le_compat_l.
apply le_0_n.
intro hom. destruct hom. simpl. rename m0 into n.
apply (le_trans _ (n+o) _). apply IHhon. auto. auto.
rename m0 into n.
apply (le_trans _ (n + S m) _).
apply IHhon. apply (le_trans _ m _). assumption. auto.
simpl. rewrite plus_comm at 2. simpl. rewrite plus_comm. simpl. auto.
Qed.

Theorem all1orgt2 : forall (c:com), count_all c = 1 \/ count_all c > 2.
unfold gt. unfold lt.
induction c. simpl. left. reflexivity.
right. inversion IHc1 ; inversion IHc2.
simpl. rewrite H. rewrite H0. simpl. auto.
simpl. rewrite H. apply (le_trans _ (count_all c2) _). assumption. simpl. auto.
simpl. rewrite H0. apply (le_trans _ (count_all c1) _). assumption.
rewrite plus_comm. simpl. auto.
simpl. apply (le_trans _ (count_all c1+count_all c2) _).
apply all1orgt2_helper. assumption. assumption.
auto.
Qed.

End MSkipAndSeq.

Module MSkipSeqAss.

Definition state := partial_map nat.

Inductive com : Type :=
| CSkip : com
| CAss : string -> nat -> com
| CSeq : com -> com -> com
.

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall s:state, ceval CSkip s s
| E_Ass : forall (s:state) (id:string) (n:nat), ceval (CAss id n) s (update s id n)
| E_Seq : forall (src tmp dst:state) (c1 c2:com), ceval c1 src tmp -> ceval c2 tmp dst -> ceval (CSeq c1 c2) src dst
.

Fixpoint count_skip (c:com) : nat :=
match c with
| CSkip => 1
| CAss _ _ => 0
| CSeq x y => (count_skip x) + (count_skip y)
end.

Theorem no_skip_ass : forall (c:com) (src dst:state),
ceval c src dst ->
count_skip c = 0 ->
exists (s:string) (n:nat), dst s = Some n.
Proof.
intros c src dst.
generalize dependent dst.
generalize dependent src.
induction c.
simpl. intros. inversion H0.
simpl. intros. inversion H. subst s0 n0 s. exists id, n.
unfold update. unfold t_update. rewrite beq_string_refl. reflexivity.
simpl. intros.
apply MSkipAndSeq.nm0 in H0. inversion_clear H0.
inversion H. subst c0 c3 src0 dst0.
specialize (IHc2 tmp dst H7 H2).
inversion IHc2. inversion H0.
rename x into id. rename x0 into n.
exists id. exists n.
assumption.
Qed.

Fixpoint count_seq (c:com) : nat :=
match c with
| CSkip => 0
| CAss _ _ => 0
| CSeq x y => (count_seq x)+(count_seq y)+1
end.

Theorem if_ass_then_unique : forall (c:com) (src dst:state) (s:string) (n:nat),
count_seq c = 0 ->
ceval c src dst ->
(forall s:string, src s = None) ->
dst s = Some n ->
(forall (s':string) (n':nat), dst s' = Some n' -> s=s' /\ n=n').
Proof.
intros c src dst.
generalize dependent dst.
generalize dependent src.
induction c as [ | id n | ].
{
  simpl.
  intros src dst id n oo heval hnone hidn id' n' hidn'.
  (* cleanup *) clear oo.
  inversion heval as [ src' skipeq srceq srcdsteq | | ].
  (* cleanup *) clear heval skipeq. subst dst. subst src'. clear hidn'.
  (* more cleanup *) apply False_ind. clear id' n'.
  rewrite (hnone id) in hidn.
  inversion hidn.
}
{
  simpl.
  intros src dst id' n' oo heval hnone hidn' id'' n'' hidn''.
  (* cleanup *) clear oo.
  inversion heval as [ | src' id''' n''' ideq neq sind | ].
  subst id''' n'''.
  subst src'.
  rewrite <- sind in hidn'.
  rewrite <- sind in hidn''.
  (* cleanup *) clear sind.
  unfold update in hidn', hidn''.
  unfold t_update in hidn', hidn''.
  unfold beq_string in hidn', hidn''.
  destruct (string_dec id id');destruct (string_dec id id'').
  - inversion hidn''. subst n''. inversion hidn'. subst n'. subst id''. subst id'. split;reflexivity.
  - rewrite (hnone id'') in hidn''. inversion hidn''.
  - rewrite (hnone id') in hidn'. inversion hidn'.
  - rewrite (hnone id') in hidn'. inversion hidn'.
}
{
  simpl.
  intros src dst id n cso heval hnone hidn id' n' hidn'.
  apply MSkipAndSeq.nm0 in cso. inversion cso as [l r]. inversion r.
}
Qed.

End MSkipSeqAss.