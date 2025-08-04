From LogicalFoundations Require Import Basics.

Import Basics.

Theorem add_0_r : forall n: N,
  n + 0_ = n.
Proof.
  intro n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. trivial.
Qed. 

Theorem add_n_Sm : forall n m : N,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [ | n IHn ].
  - trivial.
  - simpl. rewrite IHn. trivial.
Qed. 

Theorem add_comm: forall n m : N,
  n + m = m + n.
Proof.
  intros n m. induction n as [ | n IHn ].
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn, add_n_Sm. reflexivity.
Qed.

Theorem add_assoc: forall n m p : N,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mul_0_r : forall n: N,
  n * 0_ = 0_.
Proof.
  intro n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. exact IHn.
Qed.

Fixpoint double (n: N) :=
  match n with
  | O => O
  | S v_ => S (S (double v_))
  end.

Lemma double_add : forall n, double n = n + n.
Proof.
  intro n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn, add_n_Sm. trivial.
Qed.

Lemma double_incr : forall n : N, double (S n) = S (S (double n)).
Proof.
  intro n. 
  reflexivity.
Qed. 

Theorem add_rearrange: forall n m p q : N,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite (add_comm n m).
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E; reflexivity.
Qed.

Theorem even_S : forall n : N,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [ | n IHn ]. 
  - reflexivity.
  - rewrite IHn. simpl. rewrite negb_involutive. trivial.
Qed.