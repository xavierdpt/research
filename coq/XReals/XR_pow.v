Require Export XR_R1.
Require Export XR_Rmult.

Local Open Scope R_scope.

Fixpoint pow (r:R) (n:nat) : R := match n with
| O => R1
| S n => Rmult r (pow r n)
end.
