Require Import List.

Import ListNotations.

Open Scope nat_scope.



Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al
  end.