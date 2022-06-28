
Fail #[export] Instance x : _.

Existing Class True.
(* the type is checked for typeclass-ness before interping the body so
   this is the same error *)
Fail #[export] Instance x : _ := I.
