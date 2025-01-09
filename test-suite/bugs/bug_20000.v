Module Type A.
End A.

Module Type B.
  Declare Module a : A.
End B.

Module Type C.
  Declare Module b : B.
  Module a := b.a.
End C.

Module D.
  Declare Module aa: A.
 (* Uncaught exception. Fixed by using "with Module b.a := aa" instead *)
  Fail Module Type x := C with Module a := aa.
End D.
