

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).


Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S v_ => S (S (double v_))
  end.

Theorem ev_double : forall n,
  ev (double n).
Proof.
Admitted.


(* Using Evidence in Proofs *)

Theorem le_inversion : forall (n m : nat),
  le n m -> (n = m) \/ (exists ms, m = S ms /\ le n ms).
Proof.
  intros n m H. inversion H as [ H0 | x H1 ]. 
  - left. reflexivity.
  - right. exists x. auto.
Qed.

Theorem ev_sum : forall n m, 
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2. induction H1 as [ | n H IH ].
  - apply H2.
  - simpl. apply ev_SS. apply IH.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1 H2. induction H2 as [ | n H IH ].
  - apply H1.
  - apply IH. inversion H1 as [ | r E T ]. apply E.
Qed.