Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Definition state := string -> nat.

Definition update (st:state) (id:string) (n:nat) := fun id' => if string_dec id id' then n else st id'.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AVal : string -> aexp
.

Inductive com : Type :=
| CSkip : com
| CAss : string->aexp->com
.

Inductive bexp : Type :=
| BTrue : bexp
.

Fixpoint aeval (st:state) (e:aexp) : nat :=
match e with
| ANum n => n
| AVal id => st id
end.

Fixpoint beval (st:state) (e:bexp) : bool :=
match e with
| BTrue => true
end.

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall s:state, ceval CSkip s s
| E_Ass : forall (st:state) (id:string) (n:aexp), ceval (CAss id n) st (update st id (aeval st n))
.

Definition aequiv (x y : aexp) : Prop := forall st : state, aeval st x = aeval st y.

Definition bequiv (x y : bexp) : Prop := forall st : state, beval st x = beval st y.

Definition cequiv (x y : com) : Prop := forall (src dst : state), ceval x src dst <-> ceval y src dst.

Theorem id_skip : forall (id:string), cequiv (CAss id (AVal id)) CSkip.
intro id.
unfold cequiv.
intros src dst.
split.
intro heval. inversion heval. subst id0 st. subst n.
simpl in H3. simpl.
assert (youpi : (update src id (src id)) = src).
apply functional_extensionality.
intro x. unfold update. destruct (string_dec id x). subst x. reflexivity. reflexivity.
rewrite youpi. constructor.
intro h.
assert (youpi : (update src id (aeval src (AVal id))) = dst).
inversion h. subst s. subst src. simpl. unfold update. apply functional_extensionality. intro x.
destruct (string_dec id x). subst x. reflexivity. reflexivity.
rewrite <- youpi. constructor.
Qed.


