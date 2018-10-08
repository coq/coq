
(* Bug report #3746 : Include and restricted signature *)

Module Type MT. Parameter p : nat. End MT.
Module Type EMPTY. End EMPTY.
Module Empty. End Empty.

(* Include of an applied functor with restricted sig :
   Used to create axioms (bug report #3746), now forbidden. *)

Module F (X:EMPTY) : MT.
 Definition p := 0.
End F.

Module InclFunctRestr.
 Fail Include F(Empty).
End InclFunctRestr.

(* A few variants (indirect restricted signature), also forbidden. *)

Module F1 := F.
Module F2 (X:EMPTY) := F X.

Module F3a (X:EMPTY). Definition p := 0. End F3a.
Module F3 (X:EMPTY) : MT := F3a X.

Module InclFunctRestrBis.
 Fail Include F1(Empty).
 Fail Include F2(Empty).
 Fail Include F3(Empty).
End InclFunctRestrBis.

(* Recommended workaround: manual instance before the include. *)

Module InclWorkaround.
 Module Temp := F(Empty).
 Include Temp.
End InclWorkaround.

Compute InclWorkaround.p.
Print InclWorkaround.p.
Print Assumptions InclWorkaround.p. (* Closed under the global context *)



(* Related situations which are ok, just to check *)

(* A) Include of non-functor with restricted signature :
   creates a proxy to initial stuff *)

Module M : MT.
  Definition p := 0.
End M.

Module InclNonFunct.
  Include M.
End InclNonFunct.

Definition check : InclNonFunct.p = M.p := eq_refl.
Print Assumptions InclNonFunct.p. (* Closed *)


(* B) Include of a module type with opaque content:
   The opaque content is "copy-pasted". *)

Module Type SigOpaque.
 Definition p : nat. Proof. exact 0. Qed.
End SigOpaque.

Module InclSigOpaque.
 Include SigOpaque.
End InclSigOpaque.

Compute InclSigOpaque.p.
Print InclSigOpaque.p.
Print Assumptions InclSigOpaque.p. (* Closed *)


(* C) Include of an applied functor with opaque proofs :
   opaque proof "copy-pasted" (and substituted). *)

Module F' (X:EMPTY).
 Definition p : nat. Proof. exact 0. Qed.
End F'.

Module InclFunctOpa.
 Include F'(Empty).
End InclFunctOpa.

Compute InclFunctOpa.p.
Print InclFunctOpa.p.
Print Assumptions InclFunctOpa.p. (* Closed *)
