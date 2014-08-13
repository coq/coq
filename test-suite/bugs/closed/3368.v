(* File reduced by coq-bug-finder from 7411 lines to 2271 lines., then from 889 lines to 119 lines, then from 76 lines to 19 lines *)
Set Universe Polymorphism.
Set Implicit Arguments. 
Set Primitive Projections.
Record PreCategory := { object :> Type; morphism : object -> object -> Type }.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d) }.
Definition opposite (C : PreCategory) : PreCategory := @Build_PreCategory C (fun s d => morphism C d s).
Definition opposite' C D (F : Functor C D)
  := Build_Functor (opposite C) (opposite D)
                   (object_of F)
                   (fun s d => @morphism_of C D F d s).
(* Toplevel input, characters 15-191:
Anomaly: File "pretyping/reductionops.ml", line 149, characters 4-10: Assertion failed.
Please report. *)
