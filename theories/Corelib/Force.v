Primitive Blocked@{s;u} : Univ@{s;u} -> Univ@{s;u} := #blocked_type.

Primitive Blocked_ind@{s sp;u up | s -> sp} :
  forall
    (T : Univ@{s;u})
    (P : Blocked@{s;u} T -> Univ@{sp;up})
    (IH : forall t:T, P (__block@{s;u} T t)),
    forall b, P b := #blocked_ind.
#[global] Arguments Blocked_ind {_ _} _ _.
