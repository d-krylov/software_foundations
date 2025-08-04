
Definition projection_1 P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition projection_2 P Q (HPQ : P /\ Q) : Q :=
  match HPQ with
  | conj HP HQ => HQ
  end.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R HPQ HQR => conj (projection_1 P Q HPQ) (projection_2 Q R HQR).
