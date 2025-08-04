

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