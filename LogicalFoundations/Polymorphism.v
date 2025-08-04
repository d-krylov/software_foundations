Require Import Datatypes.
Print LoadPath.

Open Scope list_scope.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y): list (X * Y) :=
  match lx, ly with
  | nil, _ => nil
  | _, nil => nil
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | (x, y) :: t_ => (x :: fst (split t_), y :: snd(split t_)) 
  end.

Compute (combine [1;2;3] [4;5;6] ).

Compute (split [(1,2); (3,4); (5,6)]).