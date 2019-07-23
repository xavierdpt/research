Require Import XR_Rlt.
Require Import XR_Rmin.
Require Import XR_Rmin_Rgt_l.
Require Import XR_Rmin_Rgt_r.

Local Open Scope R_scope.

Lemma Rmin_Rgt : forall r1 r2 r, r < Rmin r1 r2 <-> r < r1 /\ r < r2.
Proof.
  intros x y z.
  split.
  {
    intro h.
    apply Rmin_Rgt_l.
    exact h.
  }
  {
    intro h.
    apply Rmin_Rgt_r.
    exact h.
  }
Qed.