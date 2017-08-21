Class FieldType (F : Set) := mkFieldType { fldTy: F -> Set }.
Hint Mode FieldType + : typeclass_instances. (* The F parameter is an input *)

Inductive I1 := C.
Inductive I2 := .

Instance I1FieldType : FieldType I1 := { fldTy := I1_rect _ bool }.
Instance I2FieldType : FieldType I2 := { fldTy := I2_rect _ }.

Definition RecordOf F (FT: FieldType F) := forall f:F, fldTy f.

Class MapOps (M K : Set) := {
  tgtTy: K -> Set;
  update: M -> forall k:K, tgtTy k -> M
}.

Instance RecordMapOps F (FT: FieldType F) : MapOps (RecordOf F FT) F :=
{ tgtTy := fldTy; update := fun r (f: F) (x: fldTy f) z => r z }.

Axiom ex : RecordOf _ I1FieldType.

Definition works := (fun ex' => update ex' C true) (update ex C false).
Set Typeclasses Debug.
Definition doesnt := update (update ex C false) C true.
