Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Definition beq_string (x y:string) := if string_dec x y then true else false.

Theorem beq_string_refl : forall s:string, beq_string s s=true.
intro s.
unfold beq_string.
destruct (string_dec s s).
(* Case equal => true *) reflexivity.
(* Case not equal => s <> s => impossible *) contradiction.
Qed.

Theorem beq_string_true_iff: forall x y : string, beq_string x y = true <-> x=y.
intros x y.
unfold beq_string.
destruct (string_dec x y);split.
intro;assumption.
intro;reflexivity.
intro h;inversion h.
intro;subst y;contradiction.
Qed.

Theorem beq_string_false_iff: forall x y : string, beq_string x y = false <-> x<>y.
intros x y.
unfold beq_string.
destruct (string_dec x y);split.
intro h;inversion h.
intro h;subst y;contradiction.
intro;assumption.
intro;reflexivity.
Qed.

Theorem false_beq_string : forall x y, x<>y -> beq_string x y = false.
intros x y.
rewrite beq_string_false_iff.
intro;assumption.
Qed.

Definition total_map (A:Type) := string -> A.

Definition t_empty {A:Type} (v:A) : total_map A := fun _ => v.

Definition t_update {A:Type} (m:total_map A) (x:string) (v:A) := fun y => if beq_string x y then v else m y.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A := t_empty None.

Definition update {A:Type} (m:partial_map A) (x:string) (v:A) := t_update m x (Some v).

Definition update_commute {A:Type} (m:partial_map A) (x y:string) (v1 v2:A) := forall s, update( update m x v1) y v2 s = update (update m y v2) x v1 s.

(* Two consecutive updates commute when the update are performed on different identifiers *)
Theorem commute : forall (A:Type) (m:partial_map A) (x y : string) (v1 v2:A),
x<>y -> update_commute m x y v1 v2.
Proof.
unfold update_commute.
intros.
unfold update.
unfold t_update.
unfold beq_string.
destruct (string_dec x s);destruct (string_dec y s).
subst y. subst x. contradiction.
reflexivity.
reflexivity.
reflexivity.
Qed.

(* Two consecutive updates do not commute when performed on same identifier with different values *)
Theorem not_commute : forall (A:Type) (m:partial_map A) (x y : string) (v1 v2:A),
x=y /\ v1<>v2 -> not (update_commute m x y v1 v2).
Proof.
intros A m x y v1 v2.
intros [xyeq v1v2neq].
subst y.
unfold not.
unfold update_commute.
intro h.
unfold not in v1v2neq.
apply v1v2neq.
specialize (h x).
unfold update in h.
unfold t_update in h.
unfold beq_string in h.
destruct (string_dec x x).
inversion h. reflexivity.
contradiction.
Qed.

(* If two consecutive updates commute and the values are different, then the identifiers are different *)
Theorem commute_inv : forall (A:Type) (m:partial_map A) (x y : string) (v1 v2:A),
(v1<>v2 /\ update_commute m x y v1 v2)
-> x<>y.
intros A m x y a b.
intros [ha hb].
intro xyeq. subst y.
apply ha.
unfold update_commute in hb.
unfold update in hb.
unfold t_update in hb.
unfold beq_string in hb.
specialize (hb x).
destruct (string_dec x x).
inversion hb. reflexivity.
contradiction.
Qed.

(* If two consecutive updates do not commute and the identifier are the same, then the values are different *)
Theorem not_commute_inv : forall (A:Type) (m:partial_map A) (x y : string) (v1 v2:A), (x=y /\
not (update_commute m x y v1 v2)) -> v1<>v2.
intros A m x y v1 v2.
intros [ha hb].
intro hc.
apply hb. clear hb.
subst v2 y.
rename v1 into v.
unfold update_commute. intro s.
reflexivity.
Qed.

(* If two consecutive updates commute, then the values are identical or the variables are different *)
Theorem commute_then : forall (A:Type) (m:partial_map A) (x y : string) (v1 v2:A),
update_commute m x y v1 v2 -> x<>y \/ v1=v2.
intros A m x y a b.
unfold update_commute. unfold update. unfold t_update. unfold beq_string.
intro h.
specialize (h x).
destruct (string_dec y x);destruct (string_dec x x).
subst y. inversion h. subst b. right. reflexivity.
contradiction.
left. intro eq. subst y. contradiction.
contradiction.
Qed.

(* If two consecutives update do not commute, then the values are different *)
Theorem not_commute_then : forall (A:Type) (m:partial_map A) (x y : string) (v1 v2:A),
not(update_commute m x y v1 v2) -> v1<>v2.
intros A m x y v1 v2.
unfold update_commute. unfold update. unfold t_update. unfold beq_string. unfold not.
intro h.
intro heq.
apply h.
intro s.
subst v2. rename v1 into v.
destruct (string_dec y s);destruct (string_dec x s);reflexivity.
Qed.

