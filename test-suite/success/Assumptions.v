(* Test about assumptions *)

(* Test instances *)

Module Instances.

Class C' := { f' : unit }.
Class D := { g : unit }.

Module Type T. Context (c':={|f':=tt|}). Fail Definition a'' := _ : C'. End T. (* Not instance *)
Module Type U. Definition d':={|g:=tt|}. Fail Definition b'' := _ : D. End U.  (* Not instance *)

End Instances.
