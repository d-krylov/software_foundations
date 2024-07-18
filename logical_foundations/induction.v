From LF Require Export basics.

Theorem add_0_r: forall n: nat, n + 0 = n.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity. 
Qed.

(* Exercise: 2 stars, standard, especially useful (basic_induction) *)

Theorem mul_0_r: forall n: nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm: forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [ | n IHn ].
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc: forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard (double_plus) *)

Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S n_ => S (S (double n_))
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqb_refl) *)

Theorem eqb_refl: forall n: nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (even_S) *)

Fixpoint even (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n_) => even n_
  end.

Theorem negb_involutive: forall b: bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b; reflexivity.
Qed.

Theorem even_S: forall n: nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - rewrite IHn. simpl. rewrite negb_involutive. reflexivity.
Qed.

(* Exercise: 3 stars, standard, especially useful (mul_comm) *)

Theorem add_shuffle3: forall n m p: nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite add_assoc.
  assert (H: n + m = m + n).
  {
    rewrite add_comm. reflexivity. 
  }
  rewrite H. rewrite add_assoc. reflexivity.
Qed. 

Theorem n_mul_1_plus_k: forall n k: nat, 
  n * (1 + k) = n + n * k.
Proof.
  intros n k. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite add_shuffle3. rewrite <- IHn. reflexivity.
Qed.

Theorem mul_comm: forall m n: nat,
  m * n = n * m.
Proof.
  intros n m. induction m as [ | m IHm ].
  - rewrite mul_0_r. reflexivity.
  - simpl. rewrite n_mul_1_plus_k. rewrite IHm. reflexivity.
Qed.
  
(* Exercise: 2 stars, standard, optional (plus_leb_compat_l) *)

Theorem plus_leb_compat_l: forall n m p: nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [ | p IHp ].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp. reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (more_exercises) *)

Theorem leb_refl : forall n: nat,
  (n <=? n) = true.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem zero_neqb_S: forall n: nat,
  0 =? (S n) = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem andb_false_r : forall b: bool,
  andb b false = false.
Proof.
  intros b. destruct b; reflexivity. 
Qed.

Theorem S_neqb_0 : forall n: nat,
  (S n) =? 0 = false.
Proof.
  intros n. reflexivity. 
Qed.

Theorem mult_1_l : forall n: nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c: bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b, c; reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite IHn. rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc: forall n m p: nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [ | n IHn ].
  - reflexivity. 
  - simpl. rewrite mult_plus_distr_r. rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (add_shuffle3') *)

Theorem add_shuffle3': forall n m p: nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. do 2 rewrite add_assoc. 
  replace (n + m) with (m + n). reflexivity.
  rewrite add_comm. reflexivity.
Qed.

Fixpoint incr (m: bin) : bin :=
  match m with 
  | Z => B1 Z
  | B0 m_ => B1 m_
  | B1 m_ => B0 (incr m_)
  end.

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z => 0
  | B0 m_ => 2 * bin_to_nat m_
  | B1 m_ => 1 + 2 * bin_to_nat m_
  end.

Theorem bin_to_nat_pres_incr : forall b: bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b. induction b as [ | | b IHb ].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHb. do 2 rewrite add_0_r. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* Exercise: 3 stars, standard (nat_bin_nat) *)

Fixpoint nat_to_bin (n: nat) : bin :=
  match n with
  | O => Z
  | S n_ => incr (nat_to_bin n_) 
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn. reflexivity.
Qed.

Lemma double_incr : forall n: nat, double (S n) = S (S (double n)).
Proof.
  intros n. reflexivity.
Qed.

Definition double_bin (b: bin) : bin := 
  match b with
  | Z => Z
  | _ => B0 b
  end.

Example double_bin_zero : double_bin Z = Z. 
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b. simpl. induction b as [ | | b IHb ]; reflexivity.
Qed.

(* Exercise: 4 stars, advanced (bin_nat_bin) *)

Fixpoint normalize (b: bin) : bin :=
  match b with 
  | Z => Z
  | B0 b_ => double_bin (normalize b_)
  | B1 b_ => incr (normalize b_)
  end.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  Admitted.
