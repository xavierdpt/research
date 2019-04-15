Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rle.
Require Export XR_Rplus.
Require Export XR_Rplus_comm.
Require Export XR_Rplus_eq_0_l.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Rplus_eq_R0 : forall r1 r2,
  R0 <= r1 ->
  R0 <= r2 ->
  r1 + r2 = R0 ->
  r1 = R0 /\ r2 = R0.
Proof.
  intros x y.
  intros hx hy hxy.
  split.
  {
    apply Rplus_eq_0_l with y.
    { exact hx. }
    { exact hy. }
    { exact hxy. }
  } 
  {
    apply Rplus_eq_0_l with x.
    { exact hy. }
    { exact hx. }
    { rewrite Rplus_comm. exact hxy. }
  } 
Qed.

