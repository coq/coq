Module M.
  Definition t := nat.
End M.

Module Type T.
  Parameter t : Type.
End T.
Module Type TInline.
  Parameter Inline t : Type.
End TInline.

Module Make (X:T).
  Include X.
  Ltac x := unfold t.
End Make.
Module MakeInline (X:TInline).
  Include X.
  Ltac x := unfold t.
End MakeInline.

Module P := Make M.
Module PInline := MakeInline M.

Goal M.t = M.t.
Succeed progress P.x.
Succeed progress PInline.x.
Abort.
