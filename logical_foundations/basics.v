(* Exercise: 1 star, standard (nandb) *)

Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | false => true
  | true => negb b2
  end.  

Example test_nandb1: (nandb true false) = true. 
  Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true. 
  Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true. 
  Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false. 
  Proof. reflexivity. Qed.

(* Exercise: 1 star, standard (andb3) *)

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool :=
  match b1 with 
  | false => false
  | true => andb b2 b3
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => 1
  | S n_ => S n_ * factorial n_
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Fixpoint eqb (n m: nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m_ => false
         end
  | S n_ => match m with
            | O => false
            | S m_ => eqb n_ m_
            end
  end.

Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n_ =>
      match m with
      | O => false
      | S m_ => leb n_ m_
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(* Exercise: 1 star, standard (ltb) *)

Definition ltb (n m: nat) : bool := leb (S n) m.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard (plus_id_exercise) *)

Theorem plus_id_exercise: forall n m o: nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2. 
  rewrite H1. 
  rewrite H2. 
  reflexivity. 
Qed.

(* Exercise: 1 star, standard (mult_n_1) *)

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p. 
  rewrite <- mult_n_Sm. 
  rewrite <- mult_n_O. 
  reflexivity.
Qed.

(* Exercise: 2 stars, standard (andb_true_elim2) *)

Theorem andb_true_elim2: forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H. destruct b.
  - rewrite <- H. reflexivity.
  - destruct c.
    * reflexivity.
    * rewrite <- H. reflexivity.
Qed.

(* Exercise: 1 star, standard (zero_nbeq_plus_1) *)

Theorem zero_nbeq_plus_1: forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n. destruct n.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 1 star, standard (identity_fn_applied_twice) *)

Theorem identity_fn_applied_twice:
  forall (f: bool -> bool), (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f H b. rewrite H. rewrite H. reflexivity.
Qed.

(* Exercise: 1 star, standard (negation_fn_applied_twice) *)

Theorem negation_fn_applied_twice:
  forall (f: bool -> bool), (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f H b. rewrite H. rewrite H. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (andb_eq_orb) *)

Theorem andb_eq_orb:
  forall (b c: bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c. destruct b.
  - simpl. intro H. rewrite H. reflexivity.
  - simpl. intro H. rewrite H. reflexivity.
Qed.

Inductive letter : Type := | A | B | C | D | F.

Definition letter_comparison (l1 l2: letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Inductive modifier : Type := | Plus | Natural | Minus.
Inductive grade : Type := Grade (l: letter) (m: modifier).

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

(* Exercise: 1 star, standard (letter_comparison) *)

Theorem letter_comparison_Eq:
  forall l, letter_comparison l l = Eq.
Proof.
  intros l. destruct l; reflexivity.
Qed.

(* Exercise: 2 stars, standard (grade_comparison) *)

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 => 
    match letter_comparison l1 l2 with
    | Eq => modifier_comparison m1 m2
    | other => other
    end
  end.

Example test_grade_comparison1: (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
reflexivity. Qed.

Example test_grade_comparison2: (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
reflexivity. Qed.

Example test_grade_comparison3: (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
reflexivity. Qed.

Example test_grade_comparison4: (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
reflexivity. Qed.

Definition lower_letter (l: letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.

(* Exercise: 2 stars, standard (lower_letter_lowers) *)

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison F l = Lt -> letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l H. destruct l; rewrite <- H; reflexivity.
Qed.

(* Exercise: 2 stars, standard (lower_grade) *)

Definition lower_grade (g: grade) : grade :=
  match g with
  | Grade l m => match m with 
    | Plus => Grade l Natural
    | Natural => Grade l Minus
    | Minus => match l with 
      | F => Grade l m
      | _ => Grade (lower_letter l) Plus
      end
    end
  end.

Example lower_grade_A_Plus: lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.

Example lower_grade_A_Natural: lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.

Example lower_grade_A_Minus: lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lower_grade_B_Plus: lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.

Example lower_grade_F_Natural: lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.

Example lower_grade_twice: lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.

Example lower_grade_thrice: lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus: lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.

(* Exercise: 3 stars, standard (lower_grade_lowers) *)

Theorem lower_grade_lowers:
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g H. destruct g.
  - destruct l; destruct m; (try reflexivity). 
    rewrite lower_grade_F_Minus. rewrite H. reflexivity.
Qed.

Definition apply_late_policy (late_days: nat) (g: grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold:
  forall (late_days : nat) (g : grade), (apply_late_policy late_days g)
  = (if late_days <? 9 then g 
      else if late_days <? 17 then lower_grade g
      else if late_days <? 21 then lower_grade (lower_grade g)
      else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

(* Exercise: 2 stars, standard (no_penalty_for_mostly_on_time) *)

Theorem no_penalty_for_mostly_on_time:
  forall (late_days: nat) (g: grade), 
  (late_days <? 9 = true) -> apply_late_policy late_days g = g.
Proof.
  intros d g H. rewrite apply_late_policy_unfold. rewrite H. reflexivity.
Qed.

(* Exercise: 2 stars, standard (graded_lowered_once) *)

Theorem grade_lowered_once:
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros d g H1 H2 H3. rewrite apply_late_policy_unfold. rewrite H1. rewrite H2. reflexivity.
Qed.

Inductive bin: Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(* Exercise: 3 stars, standard (binary) *)

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

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
reflexivity. Qed.

Example test_bin_incr5: bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
reflexivity. Qed.

Example test_bin_incr6: bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
reflexivity. Qed.


