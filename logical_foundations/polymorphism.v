(* Exercise: 2 stars, standard (poly_exercises) *)

Inductive list (X: Type) : Type :=
  | nil
  | cons (x: X) (l: list X).

Arguments nil {X}.
Arguments cons {X}.

Fixpoint app {X : Type} (l1 l2: list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X: Type} (l: list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X: Type} (l: list X) : nat :=
  match l with
  | nil => 0
  | cons _ l_ => S (length l_)
  end.


Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(* Exercise: 2 stars, standard (poly_exercises) *)

Theorem app_nil_r : forall (X: Type), forall l: list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [ | n l IHL ].
  - reflexivity.
  - simpl. rewrite IHL. reflexivity.
Qed.

Theorem app_assoc: forall A (l m n: list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [ | x l IHL ].
  - reflexivity.
  - simpl. rewrite IHL. reflexivity.
Qed. 

Lemma app_length: forall (X: Type) (l1 l2: list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [ | n l1 IHL1 ].
  - reflexivity.
  - simpl. rewrite IHL1. reflexivity.
Qed.

(* Exercise: 2 stars, standard (more_poly_exercises) *)

Theorem rev_app_distr: forall X (l1 l2: list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [ | n l1 IHL1 ].
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHL1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall X: Type, forall l: list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [ | n l IHL ].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHL. reflexivity.
Qed.
  
Fixpoint map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

(* Exercise: 3 stars, standard (map_rev) *)

Lemma map_add: forall (X Y: Type) (f: X -> Y) (l1 l2: list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2. induction l1 as [ | n l1 IHL1 ].
  - reflexivity.
  - simpl. rewrite IHL1. reflexivity.
Qed.

Theorem map_rev: forall (X Y: Type) (f : X -> Y) (l: list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [ | n l IHL ].
  - reflexivity.
  - simpl. rewrite map_add. rewrite IHL. reflexivity.
Qed.

Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* Exercise: 2 stars, standard (fold_length) *)

Definition fold_length {X: Type} (l: list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l: list X),
  fold_length l = length l.
Proof.
  intros X l. induction l as [ | n l IHL ]. 
  - reflexivity.
  - simpl. rewrite <- IHL. reflexivity.
Qed.

(* Exercise: 3 stars, standard (fold_map) *)




