Inductive nat_product : Type :=
  | pair (n1 n2 : nat).

Definition first (p : nat_product) : nat :=
  match p with
  | pair x y => x
  end.

Definition second (p : nat_product) : nat :=
  match p with
  | pair x y => y
  end.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

