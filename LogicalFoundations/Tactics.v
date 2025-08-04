Require Import Datatypes.

From LogicalFoundations Require Import Basics.

Import Basics.

Open Scope list_scope.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true -> odd (S p) = true.
Proof.
  intros p H1 H2 H3.
  apply H2, H1, H3.
Qed.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  rewrite H2 in H1.
  injection H1 as K0 K1.
  rewrite K0, K1. trivial.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n m H.
  induction m as [ | m IHm ].
- Admitted.
  


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H.
  induction l1 as [ | l1 IHl1].
  - simpl. 