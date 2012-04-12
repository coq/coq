(* Simplified example for bug #1325 *)

(* Explanation: the proof engine see section variables as goal
   variables; especially, it can change their types so that, at
   type-checking, the section variables are not recognized
   (Typeops.check_hyps_inclusion raises "types do no match").  It
   worked before the introduction of polymorphic inductive types because
   tactics were using Typing.type_of and not Typeops.typing; the former
   was not checking hyps inclusion so that the discrepancy in the types
   of section variables seen as goal variables was not a problem (at the
   end, when the proof is completed, the section variable recovers its
   original type and all is correct for Typeops) *)

Section A.
Variable H:not True.
Lemma f:nat->nat. destruct H. exact I. Defined.
Goal f 0=f 1.
red in H.
(* next tactic was failing wrt bug #1325 because type-checking the goal
   detected a syntactically different type for the section variable H *)
case 0.
Abort.
End A.

(* Variant with polymorphic inductive types for bug #1325 *)

Section B.
Variable H:not True.
Inductive I (n:nat) : Type := C : H=H -> I n.
Goal I 0.
red in H.
case 0.
Abort.
End B.
