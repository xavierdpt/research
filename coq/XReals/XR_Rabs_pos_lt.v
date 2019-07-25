Require Import XR_Rabs.
Require Import XR_R0.
Require Import XR_Rlt.
Require Import XR_Rabs_pos.
Require Import XR_Rabs_no_R0.

Local Open Scope R_scope.

Lemma Rabs_pos_lt : forall x:R, x <> R0 -> R0 < Rabs x.
Proof.
  intros x h.
  assert (hp := Rabs_pos x).
  destruct hp as [ hp | hp ].
  { exact hp. }
  {
    assert (hn := Rabs_no_R0).
    specialize (hn _ h).
    rewrite hp in hn.
    exfalso.
    apply hn.
    reflexivity.
  }
Qed.