From Stdlib Require Import Lists.List.
Import ListNotations.

(* Exercise: product times *)

Fixpoint product {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match l1 with
  | nil => nil
  | h :: t => (map (fun y => (h, y)) l2) ++ (product t l2)
  end.

Compute product [1; 2; 3; 4] [3; 2; 1].

Lemma product_times : forall X Y (l1 : list X) (l2 : list Y),
  length (product l1 l2) = length l1 * length l2.
Proof.
  intros X Y l1 l2. induction l1 as [ | x l IHl ].
  - simpl. reflexivity.
  - simpl. rewrite length_app, IHl, length_map. reflexivity.
Qed.

(* Relating factorial to permutations *)

Fixpoint everywhere {A : Type} (a : A) (ls : list A) : list (list A) :=
  match ls with
  | [] => [[a]] | h :: t => (a :: ls) :: (map (fun ts => h :: ts) (everywhere a t))
  end.

Fixpoint concat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | a :: ls => f a ++ concat_map f ls
  end.

Fixpoint permutations {A : Type} (ls : list A) : list (list A) :=
  match ls with
  | [] => [[]] | h :: t => concat_map (everywhere h) (permutations t)
  end.

(* Exercise: permutations complete *)

Lemma In_concat_map: forall (A B : Type) (f : A -> list B) (l : list A) (y : B),
  In y (concat_map f l) -> (exists x : A, In y (f x) /\ In x l).
Proof.
  intros A B f l y H. induction l as [ | e l IHl ].
  - simpl in H. inversion H.
  - simpl in H. apply in_app_or in H. destruct H as [ I1 | I2 ].
    * exists e. split.
      + apply I1. 
      + simpl. left. reflexivity.
    * specialize (IHl I2). destruct IHl as [x [S1 S2]]. exists x. split.
      + apply S1.
      + simpl. right. apply S2.
Qed.

Lemma everywhere_perm : forall A (l1 l2 : list A) (x : A),
  In l2 (everywhere x l1) -> Permutation (x :: l1) l2.
Proof.
