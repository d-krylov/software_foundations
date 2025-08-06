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

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count_ => n :: (repeat n count_)
  end.

Fixpoint length (l: natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.


(* Exercise: list functions *)

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | x :: ls => if Nat.eqb x 0 then nonzeros ls else x :: nonzeros ls
  end.

Example test_nonzeros: nonzeros [0; 1; 0; 2; 3; 0; 0] = [1; 2; 3]. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | nil => nil
  | x :: ls => if Nat.odd x then x :: oddmembers ls else oddmembers ls
  end.

Example test_oddmembers: oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3]. reflexivity. Qed.

Definition countoddmembers (l : natlist) : nat := length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1; 0; 3; 1; 4; 5] = 4. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0; 2; 4] = 0. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0. reflexivity. Qed.

(* Exercise: alternate *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, l2_ => l2_
  | l1_, nil => l1_
  | x :: l1_, y :: l2_ => x :: y :: alternate l1_ l2_
  end.

Example test_alternate1: alternate [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6]. reflexivity. Qed.

Example test_alternate2: alternate [1] [4; 5; 6] = [1; 4; 5; 6]. reflexivity. Qed.

Example test_alternate3: alternate [1; 2; 3] [4] = [1; 4; 2; 3]. reflexivity. Qed.

Example test_alternate4: alternate [] [20; 30] = [20; 30]. reflexivity. Qed.
