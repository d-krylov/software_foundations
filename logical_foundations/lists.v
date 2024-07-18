From LF Require Export induction.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* Exercise: 1 star, standard (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall (p: natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p. reflexivity.
Qed.

(* Exercise: 1 star, standard, optional (fst_swap_is_snd) *)

Theorem fst_swap_is_snd : forall (p: natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros. destruct p. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l: natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2: natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

(* Exercise: 2 stars, standard, especially useful (list_funs) *)

Fixpoint nonzeros (l: natlist) : natlist :=
  match l with
  | nil => nil
  | n_ :: l_ => match n_ with
                | O => nonzeros l_
                | _ => n_ :: nonzeros l_ 
                end
  end.

Example test_nonzeros:
  nonzeros [0; 1; 0; 2; 3; 0; 0] = [1; 2; 3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l: natlist) : natlist :=
  match l with
  | nil => nil
  | n_ :: l_ => match even n_ with
                | true => oddmembers l_
                | false => n_ :: oddmembers l_
                end
  end.

Example test_oddmembers:
  oddmembers [0; 1; 0; 2; 3; 0; 0] = [1; 3].
Proof. reflexivity. Qed.

Definition countoddmembers (l: natlist) : nat := length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1; 0; 3; 1; 4; 5] = 4.
Proof. reflexivity. Qed.
  
Example test_countoddmembers2:
  countoddmembers [0; 2; 4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* Exercise: 3 stars, advanced (alternate) *)

Fixpoint alternate (l1 l2: natlist) : natlist :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | n1 :: l1_, n2 :: l2_ => n1 :: n2 :: alternate l1_ l2_
  end.

Example test_alternate1:
  alternate [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4; 5; 6] = [1; 4; 5; 6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1; 2; 3] [4] = [1; 4; 2; 3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20; 30] = [20; 30].
Proof. reflexivity. Qed.

(* Exercise: 3 stars, standard, especially useful (bag_functions) *)

Definition bag := natlist.

Fixpoint count (v: nat) (s: bag) : nat :=
  match s with
  | nil => 0
  | n_ :: s_ => match eqb n_ v with
                | true => 1 + count v s_
                | false => count v s_
                end
  end.

Example test_count1: count 1 [1; 2; 3; 1; 4; 1] = 3.
  Proof. reflexivity. Qed.

Example test_count2: count 6 [1; 2; 3; 1; 4; 1] = 0.
  Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := alternate.

Example test_sum1: count 1 (sum [1; 2; 3] [1; 4; 1]) = 3.
  Proof. reflexivity. Qed.

Definition add (v: nat) (s: bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1; 4; 1]) = 3.
  Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1; 4; 1]) = 0.
  Proof. reflexivity. Qed.

Fixpoint member (v: nat) (s: bag) : bool :=
  match s with
  | nil => false
  | n_ :: s_ => match eqb n_ v with
                | true => true
                | false => member v s_
                end
  end.

Example test_member1: member 1 [1; 4; 1] = true.
  Proof. reflexivity. Qed.

Example test_member2: member 2 [1; 4; 1] = false.
  Proof. reflexivity. Qed.

(* Exercise: 3 stars, standard, optional (bag_more_functions) *)

Fixpoint remove_one (v: nat) (s: bag) : bag :=
  match s with
  | nil => nil
  | n_ :: s_ => match eqb n_ v with
                | true => s_
                | false => n_ :: remove_one v s_
                end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2; 1; 5; 4; 1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2; 1; 4; 1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2; 1; 4; 5; 1; 4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2; 1; 5; 4; 5; 1; 4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v: nat) (s: bag) : bag :=
  match s with
  | nil => nil
  | n_ :: s_ => match eqb n_ v with
                | true => remove_all v s_
                | false => n_ :: remove_all v s_
                end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2; 1; 5; 4; 1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2; 1; 4; 1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2; 1; 4; 5; 1; 4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2; 1; 5; 4; 5; 1; 4; 5; 1; 4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1: bag) (s2: bag) : bool :=
  match s1 with
  | nil => true
  | n1 :: s1_ => match member n1 s2 with
                 | true => included s1_ (remove_one n1 s2)
                 | false => false
                 end
  end.

Example test_included1: included [1; 2] [2; 1; 4; 1] = true.
Proof. reflexivity. Qed.

Example test_included2: included [1;2;2] [2; 1; 4; 1] = false.
Proof. reflexivity. Qed.

(* Exercise: 2 stars, standard, especially useful (add_inc_count) *)

Theorem add_inc_count: forall (v: nat) (s: bag),
  count v (v :: s) = 1 + count v s.
Proof.
  intros v s. simpl. rewrite eqb_refl. reflexivity.
Qed.

Fixpoint rev (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Theorem app_assoc : forall l1 l2 l3: natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [ | n l1 IHL1 ].
  - reflexivity.
  - simpl. rewrite IHL1. reflexivity. 
Qed.

(* Exercise: 3 stars, standard (list_exercises) *)

Theorem app_nil_r: forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [ | n l IHL ].
  - reflexivity.
  - simpl. rewrite IHL. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2: natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [ | n1 l1 IHL1 ].
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHL1. rewrite app_assoc. reflexivity.
Qed. 

Theorem rev_involutive : forall l: natlist,
  rev (rev l) = l.
Proof.
  intros. induction l as [ | n l IHL ].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHL. reflexivity.
Qed.

Theorem app_assoc4: forall l1 l2 l3 l4: natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [ | n l1 IHL1 ].
  - rewrite app_assoc. reflexivity.
  - simpl. rewrite IHL1. reflexivity.
Qed.

Lemma nonzeros_app: forall l1 l2: natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [ | n l1 IHL1 ].
  - reflexivity.
  - simpl. destruct n; rewrite IHL1; reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqblist) *)

Fixpoint eqblist (l1 l2: natlist) : bool := 
  match l1, l2 with
  | nil, nil => true
  | _, nil => false
  | nil, _ => false
  | n1 :: l1_, n2 :: l2_ => match eqb n1 n2 with
                            | true => eqblist l1_ l2_
                            | false => false
                            end
  end.

Example test_eqblist1 : (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_eqblist2 : eqblist [1; 2; 3] [1; 2; 3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 : eqblist [1; 2; 3] [1; 2; 4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l: natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [ | n l IHL ].
  - reflexivity.
  - simpl. rewrite eqb_refl. rewrite IHL. reflexivity.
Qed.

(* Exercise: 1 star, standard (count_member_nonzero) *)

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. reflexivity.
Qed.

(* Exercise: 3 stars, advanced (remove_does_not_increase_count) *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [ | n IHn ].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity. 
Qed.

Theorem remove_does_not_increase_count: forall (s: bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [ | n s IHs ].
  - reflexivity.
  - simpl. destruct n.
    * rewrite leb_n_Sn. reflexivity.
    * simpl. rewrite IHs. reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (bag_count_sum) *)

Theorem bag_count_sum: forall (n: nat) (s1 s2 : bag),
  count n (s1 ++ s2) = count n s1 + count n s2.
Proof.
  intros n s1 s2. induction s1 as [ | m1 s1 IHs1 ].
  - reflexivity.
  - simpl. destruct (m1 =? n); rewrite IHs1; reflexivity.
Qed.

(* Exercise: 3 stars, advanced (involution_injective) *)

Theorem involution_injective : forall (f: nat -> nat),
  (forall n: nat, n = f (f n)) -> (forall n1 n2: nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H1 n1 n2 H2. rewrite H1. rewrite <- H2. rewrite <- H1. reflexivity.
Qed.

(* Exercise: 2 stars, advanced (rev_injective) *) 

Theorem rev_injective : forall (l1 l2: natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H. rewrite <- rev_involutive. rewrite <- H. rewrite rev_involutive. reflexivity.
Qed.

