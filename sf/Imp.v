Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Maps.
Require Import Coq.Logic.FunctionalExtensionality.

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

End MSkipAndSeq.