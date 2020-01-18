(* Test about assumptions *)

(* Test instances *)

Module Instances.

Class C' := { f' : unit }.
Class D := { g : unit }.

Module Type T. Context (c':={|f':=tt|}). Fail Definition a'' := _ : C'. End T. (* Not instance *)
Module Type U. Definition d':={|g:=tt|}. Fail Definition b'' := _ : D. End U.  (* Not instance *)

(* Local assumptions are always instances by default *)
(* Global assumptions are instances if using Context *)

Class C := { f : unit }.
Section A. Context (c:C). Definition a := _ : C. End A.                       (* Instance *)
Section B. Variable d:D. Definition b := _ : D. End B.                        (* Instance *)
Context (c:C). Definition a0 := _ : C.                                        (* Instance *)
Parameter d:D. Fail Definition b0 := _ : D.                                   (* Not instance *)

(* Local/global definitions are never instances by default, using Context or not *)

Section A'. Context (c':={|f':=tt|}). Fail Definition a' := _ : C'. End A'.   (* Not instance *)
Section B'. Let d:={|g:=tt|}. Fail Definition b' := _ : D. End B'.            (* Not instance *)
Context (c':={|f':=tt|}). Fail Definition a0' := _ : C'.                      (* Not instance *)
Definition d':={|g:=tt|}. Fail Definition b0' := _ : D.                       (* Not instance *)

End Instances.
