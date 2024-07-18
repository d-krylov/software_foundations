From LF Require Export induction.

Inductive ev: nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n: nat) (H: ev n) : ev (S (S n)).


(* Exercise: 1 star, standard (ev_double) *)

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [ | n IHn ].
  - apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

(* Exercise: 1 star, standard (inversion_practice) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. 
  inversion H as [ | n1 H1 E1 ]. 
  inversion H1 as [ | n2 H2 E2]. 
  apply H2.
Qed.

(* Exercise: 2 stars, standard (ev_sum) *)

Theorem ev_sum: forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2. induction H1.
  - apply H2.
  - simpl. apply ev_SS. apply IHev.
Qed.

(* Exercise: 4 stars, advanced, optional (ev'_ev) *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros H. induction H as [ | | n m Hn IHev1 Hm IHev2].
    * apply ev_0.
    * apply ev_SS. apply ev_0.
    * apply ev_sum. apply IHev1. apply IHev2.
  - intros H. induction H as [ | n H IHev ].
    * apply ev'_0.
    * Admitted.