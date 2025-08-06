From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.
Import ListNotations.

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
  | perm_nil: Permutation [] []
  | perm_skip : forall x l ls, Permutation l ls -> Permutation (x :: l) (x :: ls)
  | perm_swap : forall x y l, Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l ls lss, Permutation l ls -> Permutation ls lss -> Permutation l lss.

Theorem Permutation_refl : forall A (l : list A),
  Permutation l l.
Proof.
  intros A l. induction l as [ | x l IHl ].
  - apply perm_nil.
  - apply perm_skip, IHl.
Qed.

Theorem Permutation_length : forall A (l1 l2 : list A),
  Permutation l1 l2 -> length l1 = length l2.
Proof.
  intros A l1 l2 H. induction H as [  | x l ls H1 IH1 | | l ls lss H1 H2 H3 IH2 ].
  - reflexivity.
  - simpl. rewrite IH1. reflexivity.
  - reflexivity.
  - rewrite H2, IH2. reflexivity.
Qed.

Lemma Permutation_sym : forall A (l1 l2 : list A),
  Permutation l1 l2 -> Permutation l2 l1.
Proof.
  intros A l1 l2 H. induction H as [  | x l ls H1 IH1 | | l ls lss H1 H2 H3 IH2 ].
  - apply perm_nil.
  - apply perm_skip, IH1.
  - apply perm_swap.
  - apply perm_trans with (ls := ls). exact IH2. exact H2.
Qed.

Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
  | Forall_nil : Forall P []
  | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l).

Theorem Forall_perm: forall A (f: A -> Prop) al bl,
  Permutation al bl -> Forall f al -> Forall f bl.
Proof.
  intros A f al bl H1 H2. Admitted.

(* The Insertion-Sort Program *)

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | nil => i :: nil
  | h :: t => if leb i h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (sort t)
  end.

(* Specification of Correctness *)

Inductive sorted: list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_1 : forall x, sorted [x]
  | sorted_cons : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

(* Proof of Correctness *)

Lemma insert_perm: forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [ | e l IHl ].
  - apply perm_skip, perm_nil.
  - simpl. destruct (leb x e).
    * apply Permutation_refl.
    * apply perm_trans with (ls := e :: x :: l). 
      apply perm_swap.
      apply perm_skip.
      apply IHl.
Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l. induction l as [ | x l IHl ].
  - apply perm_nil.
  - simpl. 
    apply perm_trans with (ls := x :: sort l). 
    apply perm_skip.
    apply IHl.
    apply insert_perm.
Qed.

Lemma insert_sorted: forall a l,
  sorted l -> sorted (insert a l).
Proof.
  intros a l H. Admitted.


