From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.

(* The Selection-Sort Program *)

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, ls) := select x t
         in (j, h :: ls)
    else let (j, ls) := select h t
         in (j, x :: ls)
  end.


(* Proof of Correctness *)

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Lemma select_perm: forall x l y r,
  select x l = (y, r) -> Permutation (x :: l) (y :: r).
Proof.
  intros x l y r H. induction l as [ | e l IHl ]. Admitted.

Lemma select_rest_length : forall x l y r,
  select x l = (y, r) -> length l = length r.
Proof.
  Admitted.