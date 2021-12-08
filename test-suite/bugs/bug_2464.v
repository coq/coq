Require Import FSetWeakList.
Require Import FSetDecide.

Parameter Name : Set.
Axiom eq_Name_dec : forall (n : Name) (o : Name), {n = o} + {n <> o}.

Module DecidableName.
Definition t := Name.
Definition eq := @eq Name.
Definition eq_refl := @refl_equal Name.
Definition eq_sym := @sym_eq Name.
Definition eq_trans := @trans_eq Name.
Definition eq_dec := eq_Name_dec.
End DecidableName.

Module NameSetMod := Make(DecidableName).

Module NameSetDec := WDecide (NameSetMod).

Class PartPatchUniverse (pu_type1 pu_type2 : Type)
                       : Type := mkPartPatchUniverse {
}.
Class PatchUniverse {pu_type : Type}
                    (ppu : PartPatchUniverse pu_type pu_type)
                  : Type := mkPatchUniverse {
    pu_nameOf : pu_type -> Name
}.

Lemma foo : forall (pu_type : Type)
                   (ppu : PartPatchUniverse pu_type pu_type)
                   (patchUniverse : PatchUniverse ppu)
                   (ns ns1 ns2 : NameSetMod.t)
                   (containsOK : NameSetMod.Equal ns1 ns2)
                   (p : pu_type)
                   (HX1 : NameSetMod.Equal ns1 (NameSetMod.add (pu_nameOf p) ns)),
            NameSetMod.Equal ns2 (NameSetMod.add (pu_nameOf p) ns).
Proof.
NameSetDec.fsetdec.
Qed.
