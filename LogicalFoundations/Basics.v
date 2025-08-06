Require Import Datatypes.
Require Import Nat.

Module Basics.

Inductive N: Type := 
  | O : N
  | S : N -> N.

Inductive bin: Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint to_nat (n: N) : nat :=
  match n with
  | O => 0
  | S v_ => succ (to_nat v_)
  end.

Fixpoint from_nat (n: nat) : N :=
  match n with
  | 0 => O
  | Datatypes.S v_ => S (from_nat v_)
  end.

Compute to_nat (S (S (S O))).

Compute from_nat 5.

Fixpoint add (n : N) (m : N) : N :=
  match n with
  | O => m
  | S v_ => S (add v_ m)
  end.

Fixpoint mul (n m : N) : N :=
  match n with
  | O => O
  | S v_ => add m (mul v_ m)
  end.

Notation "x + y" := (add x y) (at level 50, left associativity).
Notation "x * y" := (mul x y) (at level 40, left associativity).
Notation "0_" := O.
Notation "1_" := (S O).
Notation "2_" := (S (S O)).

Fixpoint even (n: N) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S v_) => even v_
  end.

Definition odd (n: N) : bool := negb (even n).

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z => 0
  | B0 m_ => 2 * bin_to_nat m_
  | B1 m_ => 1 + 2 * bin_to_nat m_
  end.

End Basics.


