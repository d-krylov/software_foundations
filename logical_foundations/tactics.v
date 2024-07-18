From LF Require Export polymorphism.
From LF Require Export basics.

Theorem rev_exercise1 : forall (l r: list nat),
  l = rev r -> r = rev l.
Proof.
  intros l r H. rewrite H. symmetry. apply rev_involutive.
Qed.

(* Exercise: 3 stars, standard, optional (trans_eq_exercise) *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n_) => n_
  end.

Example trans_eq_exercise: forall (n m o p: nat),
  m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2. transitivity m. apply H2.  apply H1.
Qed.

(* Exercise: 3 stars, standard (injection_ex3) *)

Example injection_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros X x y z l j H. 
  injection H as G1. rewrite <- H. intros G2. 
  injection G2. intros G3. rewrite G3. apply G1.
Qed.

(* Exercise: 1 star, standard (discriminate_ex3) *)

Example discriminate_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j H. discriminate H.
Qed.

(* Exercise: 2 stars, standard (eqb_true) *)

Theorem eqb_true: forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [ | n IHn ].
  - destruct m; intros H.
    * reflexivity. 
    * discriminate H.
  - simpl. intros m. destruct m.
    * intros H. discriminate H.
    * intros H. f_equal. apply IHn. apply H.
Qed.

(* Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
Proof.
  Admitted.