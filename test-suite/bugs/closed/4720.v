(** Bug 4720 : extraction and "with" in module type *)

Module Type A.
 Parameter t : Set.
End A.

Module A_instance <: A.
 Definition t := nat.
End A_instance.

Module A_private : A.
 Definition t := nat.
End A_private.

Module Type B.
End B.

Module Type C (b : B).
 Declare Module a : A.
End C.

Module WithMod (a' : A) (b' : B) (c' : C b' with Module a := A_instance).
End WithMod.

Module WithDef (a' : A) (b' : B) (c' : C b' with Definition a.t := nat).
End WithDef.

Module WithModPriv (a' : A) (b' : B) (c' : C b' with Module a := A_private).
End WithModPriv.

(* The initial bug report was concerning the extraction of WithModPriv
   in Coq 8.4, which was suboptimal: it was compiling, but could have been
   turned into some faulty code since A_private and c'.a were not seen as
   identical by the extraction.

   In Coq 8.5 and 8.6, the extractions of WithMod, WithDef, WithModPriv
   were all causing Anomaly or Assert Failure. This shoud be fixed now.
*)

Require Extraction.

Recursive Extraction WithMod.

Recursive Extraction WithDef.

Recursive Extraction WithModPriv.

(* Let's even check that all this extracted code is actually compilable: *)

Extraction TestCompile WithMod WithDef WithModPriv.
