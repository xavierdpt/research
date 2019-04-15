Require Import XR_R.
Require Import XR_bound.
Require Import XR_is_lub.

Local Open Scope R_scope.

Axiom completeness : forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.
