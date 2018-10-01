Require Import Coq.Setoids.Setoid.

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

Theorem app_length : forall la lb : natlist,
  length (app la lb) = (length la) + (length lb).
Proof.
induction la. reflexivity.
intro lb. simpl. rewrite IHla. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
induction l. reflexivity.
simpl. rewrite app_length. simpl. rewrite IHl. simpl.
rewrite Induction.plus_comm. simpl. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  app l nil = l.
Proof.
induction l. reflexivity.
simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall la lb : natlist,
  rev (app la lb) = app (rev lb) (rev la).
Proof.
induction la.
- simpl. intro lb. rewrite app_nil_r. reflexivity.
- intro lb. simpl. rewrite IHla. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
induction l. reflexivity.
simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall la lb lc ld : natlist,
  app la (app lb (app lc ld)) = app (app (app la lb) lc) ld.
Proof.
induction la. intros lb lc ld. simpl. rewrite app_assoc. reflexivity.
intros lb lc ld. simpl. rewrite (IHla lb lc ld). reflexivity.
Qed.

Lemma nonzeros_app : forall la lb : natlist,
  nonzeros (app la lb) = app (nonzeros la) (nonzeros lb).
Proof.
induction la. simpl. reflexivity.
intro lb. destruct n. simpl. rewrite IHla. reflexivity.
simpl. rewrite IHla. reflexivity.
Qed.

Fixpoint beq_nat (a b:nat) : bool :=
match a, b with
| O, O => true
| O, S _ => false
| S _, O => false
| S a', S b' => beq_nat a' b'
end.

Theorem beq_nat_refl : forall n:nat, beq_nat n n = true.
Proof.
induction n.
- reflexivity.
- simpl. assumption.
Qed.

Fixpoint beq_natlist (la lb : natlist) : bool :=
match la, lb with
| nil, nil => true
| cons _ _, nil => false
| nil, cons _ _ => false
| cons ha ta, cons hb tb => if beq_nat ha hb then beq_natlist ta tb else false
end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist (cons 1 (cons 2 (cons 3 nil))) (cons 1 (cons 2 (cons 3 nil))) = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist (cons 1 (cons 2 (cons 3 nil))) (cons 1 (cons 2 (cons 4 nil))) = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
induction l.
- reflexivity.
- rewrite IHl. simpl. rewrite beq_nat_refl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  Nat.leb 1 (count 1 (cons 1 s)) = true.
Proof.
induction s.
- reflexivity.
- reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  Nat.leb n (S n) = true.
Proof.
induction n.
- reflexivity.
- simpl. assumption.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  Nat.leb (count 0 (remove_one 0 s)) (count 0 s) = true.
(* Stuck ; maybe something's wrong *) Admitted.

Theorem rev_injective : forall (la lb : natlist), rev la = rev lb -> la = lb.
Proof.
induction la.
- simpl. intros.
Search "rev".
rewrite <- rev_involutive.
rewrite <- H. simpl. reflexivity.
- intros. rewrite <- rev_involutive. rewrite <- H. rewrite rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | cons a l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error (cons 4 (cons 5 (cons 6 (cons 7 nil)))) 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error (cons 4 (cons 5 (cons 6 (cons 7 nil)))) 3 = Some 7.
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error (cons 4 (cons 5 (cons 6 (cons 7 nil)))) 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
match l with
| nil => None
| cons h t => Some h
end.

Example test_hd_error1 : hd_error nil = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error (cons 1 nil) = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error (cons 5 (cons 6 nil)) = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
induction l.
reflexivity.
reflexivity.
Qed.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
intro id. destruct id.
simpl. rewrite beq_nat_refl. reflexivity.
Qed.

Module PartialMap.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
simpl. intros. rewrite <- beq_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
intros. simpl. rewrite H. reflexivity.
Qed.

End PartialMap.

End Lists.

Module Poly.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X:Type} (x:X) (count:nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.

Example test_repeat1 :
  repeat 4 2 = cons 4 (cons 4 nil).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat false 1 = cons false nil .
Proof. reflexivity. Qed.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  app l nil = l.
Proof.
induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  app l (app m n) = app (app l m) n.
Proof.
induction l. reflexivity.
intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (app l1 l2) = length l1 + length l2.
Proof.
intros X la.
induction la.
reflexivity.
intros lb.
simpl. rewrite IHla. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
intros X la.
induction la. intro lb. simpl. rewrite app_nil_r. reflexivity.
simpl. intro lb.
specialize (IHla lb).
rewrite IHla. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
intros X.
induction l. reflexivity.
simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition fst {X Y : Type} (p : prod X Y) : X :=
  match p with
  | pair x y => x
  end.

Definition snd {X Y : Type} (p : prod X Y) : Y :=
  match p with
  | pair x y => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (prod X Y) :=
  match lx, ly with
  | nil, _ => nil
  | _, nil => nil
  | cons x tx, cons y ty => cons (pair x y) (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (prod X Y))
               : prod (list X) (list Y) :=
match l with
| nil => pair nil nil
| cons (pair x y) t => let tp := split t in (pair (cons x (fst tp)) (cons y (snd tp)))
end.

Example test_split:
  split (cons (pair 1 false) (cons (pair 2 false) nil)) = pair (cons 1 (cons 2 nil)) (cons false (cons false nil)).
Proof. reflexivity. Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | cons a l' => if Lists.beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error (cons 4 (cons 5 (cons 6 (cons 7 nil)))) 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error (cons (cons 1 nil) (cons (cons 2 nil) nil)) 1 = Some (cons 2 nil).
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error (cons true nil) 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
match l with
| nil => None
| cons h t => Some h
end.

Example test_hd_error1 : hd_error (cons 1 (cons 2 nil)) = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error (cons (cons 1 nil) (cons (cons 2 nil) nil)) = Some (cons 1 nil).
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Example test_doit3times: doit3times Basics.minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | nil => nil
  | cons h t => if test h then cons h (filter test t)
                        else filter test t
  end.

Definition evenb (n:nat) := if Basics.evenb n then true else false.

Example test_filter1: filter evenb (cons 1 (cons 2 (cons 3 (cons 4 nil)))) = (cons 2 (cons 4 nil)).
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  Lists.beq_nat (length l) 1.

Example test_filter2:
let l1 := (cons 1 (cons 2 nil)) in
let l2 := (cons 3 nil) in
let l3 := (cons 4 nil) in
let l4 := (cons 5 (cons 6 (cons 7 nil))) in
let l5 := @nil nat in
let l6 := (cons 8 nil) in
filter length_is_1 (cons l1 (cons l2 (cons l3 (cons l4 (cons l5 (cons l6 nil))))))
 = (cons l2 (cons l3 (cons l6 nil))).
Proof. reflexivity. Qed.

Definition oddb (n:nat) : bool := if Basics.oddb n then true else false.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' (cons 1 (cons 0 (cons 3 (cons 1 (cons 4 (cons 5 nil)))))) = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' (cons 0 (cons 2 (cons 4 nil))) = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
let l1 := (cons 1 (cons 2 nil)) in
let l2 := (cons 3 nil) in
let l3 := (cons 4 nil) in
let l4 := (cons 5 (cons 6 (cons 7 nil))) in
let l5 := @nil nat in
let l6 := (cons 8 nil) in
    filter (fun l => Lists.beq_nat (length l) 1)
           (cons l1 (cons l2 (cons l3 (cons l4 (cons l5 (cons l6 nil))))))
  = (cons l2 (cons l3 (cons l6 nil))).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | nil => nil
  | cons h t => cons (f h) (map f t)
  end.

Theorem map_app_distr : forall (X Y : Type) (f : X -> Y) (l m : list X),
map f (app l m) = app (map f l) (map f m).
intros X Y f.
induction l. reflexivity.
intros m. simpl.
rewrite IHl. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros X Y f.
induction l.
- reflexivity.
- simpl.
rewrite map_app_distr.
rewrite <- IHl.
simpl. reflexivity. 
Qed.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | cons h t => f h (fold f t b)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
intros X.
induction l. reflexivity.
simpl. rewrite <- IHl.
unfold fold_length at 1. simpl. unfold fold_length at 1. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y.
Admitted.

Theorem fold_map_correct : False.
Admitted.

Definition prod_curry {X Y Z : Type}
  (f : (prod X Y) -> Z) (x : X) (y : Y) : Z := f (pair x y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : prod X Y) : Z := f (fst p) (snd p).

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
intros X Y Z f x y.
unfold prod_curry, prod_uncurry.
simpl. reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (prod X Y) -> Z) (p : prod X Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
intros X Y Z f p.
destruct p. unfold prod_uncurry, prod_curry. simpl. reflexivity.
Qed.

Theorem nth_error_toofar : forall X n l, length l = n -> @nth_error X l n = None.
intros X n l. generalize dependent n. induction l.
simpl. reflexivity.
intros n heq.
simpl in heq. destruct n. inversion heq.
inversion heq. specialize (IHl n H0).
simpl. rewrite H0. assumption.
Qed.

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f(f (f x)).

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition succ (n : nat) : nat := fun (X : Type) (f : X -> X) (x : X) => f(n X f x).


Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat :=
fun (X : Type) (f : X -> X) (x : X) => (m X f (n X f x)).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

End Church.

(* Multiplication and exponentiation skipped *)

End Poly.

Module Tactics.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     (cons n (cons o nil)) = (cons n (cons p nil)) ->
     (cons n (cons o nil)) = (cons m (cons p nil)).
Proof.
intros. subst m. assumption.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> (cons q (cons o nil)) = (cons r (cons p nil))) ->
     (cons n (cons o nil)) = (cons m (cons p nil)).
Proof.
intros.
subst m. apply H0. reflexivity.
Qed.

Theorem silly2a : forall (n m : nat),
     (pair n n) = (pair m m) ->
     (forall (q r : nat), (pair q q) = (pair r r) -> (cons q nil) = (cons r nil)) ->
     (cons n nil) = (cons m nil).
Proof.
intros n m. intro heq. inversion heq. subst m. clear heq H1.
intro h. apply h. reflexivity.
Qed.

Search "beq_nat".

Theorem silly3_firsttry : forall (n : nat),
     true = Lists.beq_nat n 5 ->
     Lists.beq_nat (S (S n)) 7 = true.
Proof.
intros n h. symmetry. simpl. apply h.
Qed.

Theorem rev_exercise1 : forall (l l' : Poly.list nat),
     l = Poly.rev l' ->
     l' = Poly.rev l.
Proof.
intros l l' h.
subst l. rewrite Poly.rev_involutive. reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
(cons a (cons b nil)) = (cons c (cons d nil)) ->
(cons c (cons d nil)) = (cons e (cons f nil)) ->
(cons a (cons b nil)) = (cons e (cons f nil)).
Proof.
intros. rewrite H. rewrite H0. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
intros. rewrite H. rewrite H0. reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
(cons a (cons b nil)) = (cons c (cons d nil)) ->
(cons c (cons d nil)) = (cons e (cons f nil)) ->
(cons a (cons b nil)) = (cons e (cons f nil)).
Proof.
intros. eapply trans_eq. eassumption. eassumption.
Qed.

Search "minustwo".

Example trans_eq_exercise : forall (n m o p : nat),
     m = (Basics.minustwo o) ->
     (n + p) = m ->
     (n + p) = (Basics.minustwo o).
Proof.
intros.
subst m. assumption.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
intros.
inversion H. reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  (cons n (cons m nil)) = (cons o (cons o nil)) ->
  (cons n nil) = (cons m nil).
Proof.
intros. inversion H. reflexivity.
Qed.

Example inversion_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
  (cons x (cons y  l)) = (cons w (cons z  j)) ->
  (cons x l) = (cons z j) ->
  x = y.
Proof.
intros.
inversion H0. subst j. subst z.
inversion H. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
   Lists.beq_nat 0 n = true -> n = 0.
Proof.
intros.
destruct n. reflexivity. simpl in H. inversion H.
Qed.

Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  (cons x (cons y l)) = nil ->
  cons y l = cons z j ->
  x = z.
Proof.
intros. inversion H. Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
intros. subst y. reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     Lists.beq_nat (S n) (S m) = b ->
     Lists.beq_nat n m = b.
Proof.
intros.
simpl in H. assumption.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
induction n. destruct m. reflexivity. simpl. intro h;inversion h.
destruct m. simpl. intro h;inversion h.
simpl. intro h.
inversion h. clear h.
Search "plus_comm".
rewrite Induction.plus_comm in H0 . simpl in H0.
symmetry in H0.
rewrite Induction.plus_comm in H0. simpl in H0. inversion H0.
specialize (IHn m). symmetry in H1. specialize (IHn H1). subst m. reflexivity.
Qed.

Definition double := Induction.double.

Theorem double_injective: forall n m,
      double n = double m -> n = m.
intro n. induction n.
simpl. destruct m. reflexivity. simpl. intro h;inversion h.
intros m h.
simpl in h.
destruct m. inversion h.
simpl in h. inversion h.
specialize (IHn m H0). subst m. reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
    Lists.beq_nat n m = true -> n = m.
induction n. destruct m. reflexivity. simpl. intro h;inversion h.
simpl. destruct m. intro h;inversion h.
intro h.
rewrite (IHn m h). reflexivity.
Qed.

Theorem beq_id_true : forall x y,
  Lists.beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : Poly.list X),
     Poly.length l = n ->
     Poly.nth_error l n = None.
intros n X l.
generalize dependent n.
induction l.
simpl. reflexivity.
intros n h.
simpl. destruct n. simpl. simpl in h. inversion h.
simpl in h.
inversion h. clear h.
simpl.
rewrite H0. apply IHl. assumption.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
unfold square.
Admitted.

Fixpoint split {X Y : Type} (l : Poly.list (Poly.prod X Y))
               : prod (Poly.list X) (Poly.list Y) :=
  match l with
  | Poly.nil => pair Poly.nil Poly.nil
  | Poly.cons (Poly.pair x y) t =>
      match split t with
      | pair lx ly => pair (Poly.cons x lx) (Poly.cons y ly)
      end
  end.

Search "combine".

Theorem combine_split : forall X Y (l : Poly.list (Poly.prod X Y)) l1 l2,
  split l = pair l1 l2 ->
  Poly.combine l1 l2 = l.
Proof.
intros X Y.
induction l.
simpl. intros. inversion H. simpl. reflexivity.
intros.
destruct l1;destruct l2.
{
simpl in H. destruct x. destruct (split l). inversion H.
}
{
simpl in H. destruct x. destruct (split l). inversion H.
}
{
simpl in H. destruct x. destruct (split l). inversion H.
}
{
simpl in H. destruct x. destruct (split l). inversion H.
simpl. rewrite IHl. reflexivity.
subst l2. subst y0. subst l1. subst x0. reflexivity.
}
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
intros.
destruct (f true) eqn:eqt;destruct (f false) eqn:eqf;destruct b eqn:eqb.
rewrite eqt. rewrite eqt. rewrite eqt. reflexivity.
rewrite eqf. rewrite eqt. rewrite eqt. reflexivity.
rewrite eqt. rewrite eqt. rewrite eqt. reflexivity.
rewrite eqf. rewrite eqf. rewrite eqf. reflexivity.
rewrite eqt. rewrite eqf. rewrite eqt. reflexivity.
rewrite eqf. rewrite eqt. rewrite eqf. reflexivity.
rewrite eqt. rewrite eqf. rewrite eqf. reflexivity.
rewrite eqf. rewrite eqf. rewrite eqf. reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  Lists.beq_nat n m = Lists.beq_nat m n.
induction n. destruct m. reflexivity. simpl. reflexivity.
destruct m. simpl. reflexivity.
simpl. rewrite IHn. reflexivity.
Qed.

Theorem beq_nat_trans : forall n m p,
  Lists.beq_nat n m = true ->
  Lists.beq_nat m p = true ->
  Lists.beq_nat n p = true.
Proof.
induction n.
intros.
destruct p. reflexivity. destruct m. simpl in H0. inversion H0. simpl in H. inversion H.
intros.
simpl. destruct p. destruct m. simpl in H. inversion H. simpl in H0. inversion H0.
destruct m. simpl in H. inversion H.
apply (IHn m).
simpl in H. assumption. simpl in H0. assumption.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : Poly.list X),
     Poly.filter test l = Poly.cons x lf ->
     test x = true.
Proof.
intros X t x.
induction l.
simpl. intros. inversion H.
simpl. intros.
destruct (t x0) eqn:teq.
{
inversion H. subst x0. assumption.
}
{
eapply IHl. eassumption.
}
Qed.

Fixpoint forallb {A:Type} (l:list A) (p:A->bool) :=
match l with
| nil => true
| cons h t => if p h then forallb t p else false
end.

Fixpoint existsb {A:Type} (l:list A) (p:A->bool) :=
match l with
| nil => false
| cons h t => if p h then true else existsb t p
end.

Definition existsb' {A:Type} (l:list A) (p:A->bool) := negb (forallb l (fun x => negb (p x))).

Theorem existsb_existsb' : forall (A:Type) (l:list A) (p:A->bool), existsb l p = existsb' l p.
intros A l p. generalize dependent l.
induction l. reflexivity.
simpl. unfold existsb'. simpl.
rewrite IHl. unfold existsb'.
clear IHl.
induction l.
simpl. destruct (p a). reflexivity. reflexivity.
simpl.
destruct (p a). simpl in IHl. simpl. reflexivity.
simpl in IHl. simpl. reflexivity.
Qed.


End Tactics.

Module Logic.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
unfold injective.
intros x y h. inversion h. reflexivity.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
split;reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
intros. split;assumption.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
intro n. induction n.
simpl. intros. subst m. split;reflexivity.
intros. simpl in H. inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
intros n m [no mo].
subst n;subst m;reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
intro n. induction n. reflexivity.
intros. inversion H.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
intros P Q [p q]; assumption.
Qed.

Lemma proj2 : forall P Q : Prop,  P /\ Q -> Q.
Proof.
intros P Q [p q]; assumption.
Qed.

Theorem and_commut : forall P Q : Prop,  P /\ Q -> Q /\ P.
Proof.
intros P Q [p q]; split; assumption.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
intros P Q R [p [q r]].
split. split;assumption. assumption.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
intros n m [l|r]. subst n;reflexivity. subst m.
induction n. reflexivity. simpl. assumption.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
intros A B a. left. assumption.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
destruct n. left. reflexivity.
simpl. right. reflexivity.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),  False -> P.
intros P f. contradiction.
Qed.

Fact not_implies_our_not : forall (P:Prop),  not P -> (forall (Q:Prop), P -> Q).
Proof.
intros P hn.
intros Q p.
contradiction.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
intro heq. inversion heq.
Qed.

Theorem not_False : not False.
intro f. assumption.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,  (P /\ not P) -> Q.
Proof.
intros P Q [p np].
contradiction.
Qed.

Theorem double_neg : forall P : Prop,  P -> not (not P).
Proof.
intros P p.
intro hn. apply hn. assumption.
Qed.

Theorem contrapositive : forall (P Q : Prop),  (P -> Q) -> (not Q -> not P).
Proof.
intros P Q pq nq.
intro p. apply nq. apply pq. assumption.
Qed.

Theorem not_both_true_and_false : forall P : Prop,  not (P /\ not P).
Proof.
intros P [p np]. contradiction.
Qed.

Theorem not_true_is_false : forall b : bool,  b <> true -> b = false.
Proof.
intros b neq. destruct b. contradiction. reflexivity.
Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
intros P Q [pq qp].
split;assumption.
Qed.

Lemma not_true_iff_false : forall b,  b <> true <-> b = false.
Proof.
intro b.
split. destruct b. intro;contradiction. reflexivity.
intro. subst b. intro h;inversion h.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros P Q R.
split. intros [p | [q r]]. split;left;assumption.
split;right;assumption.
intros [ [p|q] [p'|r] ].
left;assumption.
left;assumption.
left;assumption.
right;split;assumption.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
destruct n;destruct m.
simpl. split. intros. left. reflexivity. intro. reflexivity.
simpl. split. intros. left. reflexivity. intros. reflexivity.
simpl. split. intros. right. reflexivity. intros. clear H. induction n. simpl. reflexivity. simpl. assumption.
simpl. split. intros. inversion H. intros. inversion H as [l | r]. inversion l. inversion r.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
intros P Q R.
split.
intros [p | [ q | r]].
left. left. assumption.
left. right. assumption.
right. assumption.
intros [ [ p | q ] | r ].
left. assumption.
right. left. assumption.
right. right. assumption.
Qed.

Lemma mult_0_3 : forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
intros n m p.
rewrite mult_0.
rewrite mult_0.
rewrite or_assoc.
reflexivity.
Qed.

Lemma apply_iff_example : forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
apply mult_0.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
intro n. intros [yipi yata]. subst n. exists (2+yipi). simpl. reflexivity.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not (P x)).
Proof.
intros X P h.
intros [yipi yata].
apply yata. apply h.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros X P Q.
split.
intro h. inversion_clear h as [x o].
inversion_clear o as [l|r].
left. exists x. assumption. right. exists x. assumption.
intro h. inversion_clear h as [l | r].
inversion l as [x px]. exists x. left. assumption.
inversion r as [x qx]. exists x. right. assumption.
Qed.

Fixpoint In {A : Type} (x : A) (l : Poly.list A) : Prop :=
  match l with
  | Poly.nil => False
  | Poly.cons x' l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : Poly.list A) (x : A),
    In x l ->
    In (f x) (Poly.map f l).
Proof.
intros A B f.
induction l.
simpl. intros;assumption.
simpl. intro x'. intro h.
inversion_clear h as [ ll | rr ].
subst x'. left. reflexivity.
right.
specialize (IHl x'). specialize (IHl rr). assumption.
Qed.


End V1.