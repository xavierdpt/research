
Module V1.

Module Basics.

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day
.

Definition next_weekday (d:day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| _ => monday
end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_weekday:
(next_weekday (next_weekday saturday)) = tuesday.
Proof. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool
.

Definition negb (b:bool) : bool := match b with
| true => false
| false => true
end.

Definition andb (a b:bool) : bool := match a, b with
| true, true => true
| _, _ => false
end.

Definition orb (a b:bool) : bool := match a, b with
| false, false => false
| _, _ => true
end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Example test_orb5: (orb false (orb false true)) = true.
Proof. reflexivity. Qed.

Definition nandb (a b:bool) : bool := match a, b with
| true, true => false
| _, _ => true
end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (a b c:bool) : bool :=
match a, b, c with
| true, true, true => true
| _, _, _ => false
end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.

Check (negb true).

Check negb.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb
.

Inductive color : Type :=
| black : color
| white : color
| primary : rgb -> color
.

Definition monochrome (c:color) : bool :=
match c with
| black => true
| white => true
| _ => false
end.

Definition isred (c:color) : bool :=
match c with
| primary red => true
| _ => false
end.

Module NatPlayground.

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Definition pred (n:nat) : nat :=
match n with
| O => O
| S n => n
end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n:nat) : nat :=
match n with
| O => O
| S O => O
| S (S n'') => n''
end.

Compute (minustwo 4).

Fixpoint evenb (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Definition oddb (n:nat) : bool  := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. reflexivity. Qed.

Example test_oddb2: oddb 4 = false.
Proof. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n m:nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.

Compute (plus 3 2).

Fixpoint mult (n m:nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) :=
match n, m with
| _, O => n
| O, _ => O
| S n', S m' => minus n' m'
end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
match power with
| O => S O
| S p => mult base (exp base p)
end.

Fixpoint factorial (n:nat) : nat :=
match n with
| O => 1
| S n' => mult (S n') (factorial n')
end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
match n, m with
| O, O => true
| O, _ => false
| _, O => false
| S n', S m' => beq_nat n' m'
end.

Fixpoint leb (n m:nat) :=
match n, m with
| O, O => true
| _, O => false
| O, _ => true
| S n', S m' => leb n' m'
end.

Example test_leb1: (leb 2 2) = true.
Proof. reflexivity. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. reflexivity. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m:nat) : bool :=
if beq_nat n m then false else
if leb n m then true else false.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof. intros n m eq. subst m. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros n m o nm mo.
subst o. subst m. reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof. intros n m eq. subst m. reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
intro n. destruct n;reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
intro b. destruct b;reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
intros b c.
destruct b;destruct c;reflexivity.
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
intros b c d.
destruct b;destruct c;destruct d;reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct b;destruct c;simpl;try(reflexivity);intro h;inversion h.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
intro n.
destruct n;reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
intro f.
intro hf.
intro b.
destruct b.
rewrite (hf true). rewrite (hf true). reflexivity.
rewrite (hf false). rewrite (hf false). reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
intros b c.
destruct b;destruct c;simpl;try(reflexivity);intro h;inversion h.
Qed.

End Basics.

Module Induction.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
induction n.
- reflexivity.
- simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
induction n.
- reflexivity.
- simpl. assumption.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
induction n.
- reflexivity.
- simpl. assumption.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
induction n.
- simpl. reflexivity.
- simpl. intro m. rewrite (IHn m). reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
induction n.
- simpl. induction m.
  + reflexivity.
  + simpl. rewrite <- IHm. reflexivity.
- simpl. intro m. rewrite (IHn m). rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
induction n.
simpl. reflexivity.
simpl. intros m p. rewrite (IHn m p). reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
induction n.
- reflexivity.
- simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  Basics.evenb (S n) = Basics.negb (Basics.evenb n).
induction n.
simpl. reflexivity.
destruct n. simpl. reflexivity.
rewrite IHn. simpl.
destruct (match n with | 0 => Basics.false | S n' => Basics.evenb n' end).
reflexivity. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat, Basics.true = Basics.beq_nat n n.
induction n.
simpl. reflexivity.
simpl. rewrite IHn. reflexivity.
Qed.

End Induction.

Module Lists.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod
.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
match p with
| pair x y => x
end.

Definition snd (p : natprod) : nat :=
match p with
| pair x y => y
end.

Compute (fst (pair 3 5)).

Definition swap_pair (p:natprod) : natprod :=
match p with
| pair x y => pair y x
end.

Theorem surjective_pairing : forall (p : natprod),
  p = pair (fst p) (snd p).
Proof.
intro p;destruct p. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  pair (snd p) (fst p) = swap_pair p.
Proof.
intro p;destruct p. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
intro p;destruct p. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist
.

Fixpoint repeat (n count : nat) : natlist :=
match count with
| O => nil
| S count' => cons n (repeat n count')
end.

Fixpoint length (l:natlist) : nat :=
match l with
| nil => O
| cons h t => S (length t)
end.

Fixpoint app (la lb : natlist) : natlist :=
match la with
| nil => lb
| cons ha ta => cons ha (app ta lb)
end.

Example test_app1:
app (cons 1 (cons 2 (cons 3 nil))) (cons 4 (cons 5 nil))
=
(cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil))))).
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
match l with
| nil => default
| cons h t => h
end.

Definition tl (l:natlist) : natlist :=
match l with
| nil => nil
| cons h t => t
end.

Fixpoint nonzeros (l:natlist) : natlist :=
match l with
| nil => nil
| cons O t => nonzeros t
| cons h t => cons h (nonzeros t)
end.

Example test_nonzeros:
  nonzeros (cons 0 (cons 1 (cons 0 (cons 2 (cons 3 (cons 0 (cons 0 nil))))))) = (cons 1 (cons 2 (cons 3 nil))).
reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
match l with
| nil => nil
| cons h t => if Basics.evenb h then (oddmembers t) else cons h (oddmembers t)
end.

Example test_oddmembers:
oddmembers (cons 0 (cons 1 (cons 0 (cons 2 (cons 3 (cons 0 (cons 0 nil)))))))
=
cons 1 (cons 3 nil).
reflexivity. Qed.

Definition countoddmembers (l:natlist) := length (oddmembers l).

Example test_countoddmembers1:
countoddmembers (cons 1 (cons 0 (cons 3 (cons 1 (cons 4 (cons 5 nil)))))) = 4.
reflexivity. Qed.


Example test_countoddmembers2:
countoddmembers (cons 0 (cons 2 (cons 4 nil))) = 0.
reflexivity. Qed.

Example test_countoddmembers3:
countoddmembers nil = 0.
reflexivity. Qed.

Fixpoint alternate (la lb : natlist) : natlist :=
match la, lb with
| nil, nil => nil
| cons ha ta, nil => cons ha ta
| nil, cons hb tb => cons hb tb
| cons ha ta, cons hb tb => cons ha (cons hb (alternate ta tb))
end.

Example test_alternate1:
alternate
(cons 1 (cons 2 (cons 3 nil)))
(cons 4 (cons 5 (cons 6 nil)))
=
(cons 1 (cons 4 (cons 2 (cons 5 (cons 3 (cons 6 nil)))))).
reflexivity. Qed.

Example test_alternate2:
alternate
(cons 1 nil)
(cons 4 (cons 5 (cons 6 nil)))
=
(cons 1 (cons 4 (cons 5 (cons 6 nil)))).
reflexivity. Qed.

Example test_alternate3:
alternate
(cons 1 (cons 2 (cons 3 nil)))
(cons 4 nil)
=
(cons 1 (cons 4 (cons 2 (cons 3 nil)))).
reflexivity. Qed.

Example test_alternate4:
alternate
nil
(cons 20 (cons 30 nil))
=
(cons 20 (cons 30 nil)).
reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
match s with
| nil => O
| cons h t => if Basics.beq_nat h v then S(count v t) else count v t
end.

Example test_count1: count 1 (cons 1 (cons 2 (cons 3 (cons 1 (cons 4 (cons 1 nil)))))) = 3.
reflexivity. Qed.

Example test_count2: count 6 (cons 1 (cons 2 (cons 3 (cons 1 (cons 4 (cons 1 nil)))))) = 0.
reflexivity. Qed.

Definition sum (ba bb:bag) : bag := app ba bb.

Example test_sum1: count 1 (sum (cons 1 (cons 2 (cons 3 nil))) (cons 1 (cons 4 (cons 1 nil)))) = 3.
reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 (cons 1 (cons 4 (cons 1 nil)))) = 3.
reflexivity. Qed.

Example test_add2: count 5 (add 1 (cons 1 (cons 4 (cons 1 nil)))) = 0.
reflexivity. Qed.


Definition member (v:nat) (s:bag) : bool :=
match (count v s) with
| O => false
| _ => true
end.

Example test_member1: member 1 (cons 1 (cons 4 (cons 1 nil))) = true.
reflexivity. Qed.

Example test_member2: member 2 (cons 1 (cons 4 (cons 1 nil))) = false.
reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
match s with
| nil => s
| cons h t => if Basics.beq_nat h v then t else cons h (remove_one v t)
end.

Example test_remove_one1:
  count 5 (remove_one 5
(cons 2 (cons 1 (cons 5 (cons 4 (cons 1 nil)))))
) = 0.
reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5
(cons 2 (cons 1 (cons 4 (cons 1 nil))))
) = 0.
reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5
(cons 2 (cons 1 (cons 4 (cons 5 (cons 1 (cons 4 nil))))))
) = 2.
reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5
(cons 2 (cons 1 (cons 5 (cons 4 (cons 5 (cons 1 (cons 4 nil)))))))
) = 1.
reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| cons h t => if Basics.beq_nat h v then remove_all v t else cons h (remove_all v t)
end.

Example test_remove_all1: count 5 (remove_all 5
(cons 2 (cons 1 (cons 5 (cons 4 (cons 1 nil)))))
) = 0.
reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5
(cons 2 (cons 1 (cons 4 (cons 1 nil))))
) = 0.
reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5
(cons 2 (cons 1 (cons 4 (cons 5 (cons 1 (cons 4 nil))))))
) = 2.
reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 
(cons 2 (cons 1 (cons 5 (cons 4 (cons 5 (cons 1 (cons 4 (cons 5 (cons 1 (cons 4 nil))))))))))
) = 0.
reflexivity. Qed.

Theorem nil_app : forall l:natlist,
  app nil l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
destruct l. simpl. reflexivity.
simpl. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
induction l1. simpl. reflexivity.
intros. simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Example test_rev1: rev (cons 1 (cons 2 (cons 3 nil))) = (cons 3 (cons 2 (cons 1 nil))).
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.



End Lists.

End V1.