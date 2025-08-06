From Stdlib Require Import Init.Nat.

Definition key := nat.

Inductive tree (V : Type) : Type :=
  | E
  | T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.

Arguments T {V}.

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y vs r => if x <? y then T (insert x v l) y vs r
                  else if y <? x then T l y vs (insert x v r)
                  else T l x v r
  end.

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
  | BST_E : BST E
  | BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
  ForallT P t -> forall (k : key) (v : V),
  P k v -> ForallT P (insert k v t).
Proof.
  intros V P t H1 key v H2. induction t as [ | t1 IH1 k value t2 IH2 ].
  - simpl. auto.
  - simpl. inversion H1 as [ S1 [ S2 S3 ] ]. destruct (key <? k) eqn: Eq. 
    * simpl. repeat split. apply S1. apply IH1. apply S2. apply S3.
    * destruct (k <? key) eqn: Eq1.
      + simpl. repeat split. apply S1. apply S2. apply IH2. apply S3.
      + simpl. repeat split. apply H2. apply S2. apply S3.
Qed.

Theorem insert_BST : ∀ (V : Type) (k : key) (v : V) (t : tree V),
  BST t -> BST (insert k v t).
Proof.
  Admitted.
