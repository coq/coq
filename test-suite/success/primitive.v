(* This file mostly tests for the error paths in declaring primitives.
   Successes are tested in the various test-suite/primitive/* directories *)

(* [Primitive] should be forbidden in sections, otherwise its type
after cooking will be incorrect. *)
Section S.
  Variable A : Type.
  Fail Primitive int : let x := A in Set := #int63_type.
  Fail Primitive int := #int63_type. (* we fail even if section variable not used *)
End S.
Section S.
  Fail Primitive int := #int63_type. (* we fail even if no section variables *)
End S.

(* can't declare primitives with nonsense types *)
Fail Primitive xx : nat := #int63_type.

(* non-cumulative conversion *)
Fail Primitive xx : Type@{_} := #int63_type.

(* check evars *)
Fail Primitive xx : let x := _ in Set := #int63_type.

(* explicit type is unified with expected type, not just converted

   extra universes are OK for monomorphic primitives (even though
   their usefulness is questionable, there's no difference compared
   with predeclaring them)
 *)
Primitive xx : let x := Type in _ := #int63_type.

(* double declaration *)
Fail Primitive yy := #int63_type.

Module DoubleCarry.
  (* XXX maybe should be an output test: this is the case where the new
   declaration is already in the nametab so can be nicely printed *)
  Module M.
    Variant carry (A : Type) :=
    | C0 : A -> carry A
    | C1 : A -> carry A.

    Register carry as kernel.ind_carry.
  End M.

  Module N.
    Variant carry (A : Type) :=
    | C0 : A -> carry A
    | C1 : A -> carry A.

    Fail Register carry as kernel.ind_carry.
  End N.
End DoubleCarry.

(* univ polymorphic primitives *)

(* universe count must be as expected *)
Fail Primitive array@{u v} : Type@{u} -> Type@{v} := #array_type.

(* use a phantom universe to ensure we check conversion not just the universe count *)
Fail Primitive array@{u} : Set -> Set := #array_type.

(* no constraints allowed! *)
Fail Primitive array@{u | Set < u} : Type@{u} -> Type@{u} := #array_type.

(* unification works for polymorphic primitives too (although universe
   counts mean it's not enough) *)
Fail Primitive array : let x := Type@{_} in _ -> Type@{_} := #array_type.
Primitive array : _ -> Type := #array_type.
