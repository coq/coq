Module Type TYPE.
  Parameter t : Type.
End TYPE.

Module Type A.
   Parameter t : Type.
   Parameter eqv : t -> t -> Prop.
 End A.

Module Type B (T: TYPE)
   := A with Definition t := T.t with Definition eqv := @eq T.t.
