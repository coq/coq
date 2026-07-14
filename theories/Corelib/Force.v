Primitive Blocked@{s;u} : Univ@{s;u} -> Univ@{s;u} := #blocked_type.

(* [__unblock] is block-local elaborator syntax, not a primitive constant or
   kernel term.  The reduction rule for [Blocked_ind] constructs an ordinary
   [__block] with an empty hidden-entry telescope. *)
Primitive Blocked_ind@{s sp;u up | s -> sp} :
  forall
    (T : Univ@{s;u})
    (P : Blocked@{s;u} T -> Univ@{sp;up})
    (IH : forall t:T, P (__block@{s;u} T t)),
    forall b, P b := #blocked_ind.
#[global] Arguments Blocked_ind {_ _} _ _.
