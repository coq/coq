(* Test about assumptions *)

(* Test instances *)

Module Instances.

Class C' := { f' : unit }.
Class D := { g : unit }.

Module Type T. #[warning="context-outside-section"] Context (c':={|f':=tt|}). Fail Definition a'' := _ : C'. End T. (* Not instance *)
Module Type U. Definition d':={|g:=tt|}. Fail Definition b'' := _ : D. End U.  (* Not instance *)

(* Local assumptions are always instances by default *)
(* Global assumptions are instances if using Context *)

Class C := { f : unit }.
Section A. Context (c:C). Definition a := _ : C. End A.                       (* Instance *)
Section B. Variable d:D. Definition b := _ : D. End B.                        (* Instance *)
#[warning="context-outside-section"] Context (c:C). Definition a0 := _ : C.                                        (* Instance *)
Parameter d:D. Fail Definition b0 := _ : D.                                   (* Not instance *)

(* Local/global definitions are never instances by default, using Context or not *)

Section A'. Context (c':={|f':=tt|}). Fail Definition a' := _ : C'. End A'.   (* Not instance *)
Section B'. Let d:={|g:=tt|}. Fail Definition b' := _ : D. End B'.            (* Not instance *)
#[warning="context-outside-section"] Context (c':={|f':=tt|}). Fail Definition a0' := _ : C'.                      (* Not instance *)
Definition d':={|g:=tt|}. Fail Definition b0' := _ : D.                       (* Not instance *)

End Instances.

(* Type factorization *)

Module TypeSharing. (* How to observe it? *)

Section S. Context (A B : Type). End S. (* Distinct universes *)
Section T. Variables A B : Type. End T. (* Same universe *)

Section S. Fail Context (a b : _) (e : a = 0). End S. (* not shared *)
Section S. Fail Variables (a b : _) (e : a = 0). End S. (* not shared *)

End TypeSharing.
