(* Comprehensive tests for all module signature and constraint mismatch errors *)

(* ========== signature_mismatch_error tests ========== *)

(* 1. InductiveFieldExpected - expected inductive but found definition *)
Module Type IndFieldExpType.
  Inductive I : Type := c : I.
End IndFieldExpType.
Module IndFieldExpMod.
  Definition I : Type := nat.
End IndFieldExpMod.
Fail Module IndFieldExpTest : IndFieldExpType := IndFieldExpMod.

(* 2. DefinitionFieldExpected - expected definition but found inductive *)
Module Type DefFieldExpType.
  Definition x : Type := nat.
End DefFieldExpType.
Module DefFieldExpMod.
  Inductive x : Type := c : x.
End DefFieldExpMod.
Fail Module DefFieldExpTest : DefFieldExpType := DefFieldExpMod.

(* 3. ModuleFieldExpected - expected module but found definition *)
Module Type ModFieldExpType.
  Module M.
    Definition x := 0.
  End M.
End ModFieldExpType.
Module ModFieldExpMod.
  Module M.
    Inductive x : Type := c : x.
  End M.
End ModFieldExpMod.
Fail Module ModFieldExpTest : ModFieldExpType := ModFieldExpMod.

(* 4. ModuleTypeFieldExpected - expected module type but found module *)
Module Type ModTypeFieldExpType.
  Module Type T.
    Definition x := 0.
  End T.
End ModTypeFieldExpType.
Module ModTypeFieldExpMod.
  Module T.
    Definition x := 0.
  End T.
End ModTypeFieldExpMod.
Fail Module ModTypeFieldExpTest : ModTypeFieldExpType := ModTypeFieldExpMod.

(* 5. NotConvertibleInductiveField - inductive types differ *)
Module Type NotConvIndType.
  Inductive I : Type := c : nat -> I.
End NotConvIndType.
Module NotConvIndMod.
  Inductive I : Type := c : bool -> I.
End NotConvIndMod.
Fail Module NotConvIndTest : NotConvIndType := NotConvIndMod.

(* 6. NotConvertibleConstructorField - constructor types differ *)
Module Type NotConvConsType.
  Inductive I : Type := c1 : nat -> I | c2 : I.
End NotConvConsType.
Module NotConvConsMod.
  Inductive I : Type := c1 : bool -> I | c2 : I.
End NotConvConsMod.
Fail Module NotConvConsTest : NotConvConsType := NotConvConsMod.

(* 7. NotConvertibleBodyField - definition bodies differ *)
Module Type NotConvBodyType.
  Definition x := 42.
End NotConvBodyType.
Module NotConvBodyMod.
  Definition x := 0.
End NotConvBodyMod.
Fail Module NotConvBodyTest : NotConvBodyType := NotConvBodyMod.

(* 8. NotConvertibleTypeField - definition types differ *)
Module Type NotConvTypeType.
  Definition x : nat := 0.
End NotConvTypeType.
Module NotConvTypeMod.
  Definition x : bool := true.
End NotConvTypeMod.
Fail Module NotConvTypeTest : NotConvTypeType := NotConvTypeMod.

Unset Polymorphic Inductive Cumulativity.

(* 9. CumulativeStatusExpected - expected cumulative but got non-cumulative *)
Module Type CumulExpType.
  Polymorphic Cumulative Inductive I@{u} : Type@{u} := c : I.
End CumulExpType.
Module CumulExpMod.
  Polymorphic Inductive I@{u} : Type@{u} := c : I.
End CumulExpMod.
Fail Module CumulExpTest : CumulExpType := CumulExpMod.

(* 10. PolymorphicStatusExpected - expected polymorphic but got monomorphic *)
Module Type PolyExpType.
  Polymorphic Definition x : Type := nat.
End PolyExpType.
Module PolyExpMod.
  Definition x : Type := nat.
End PolyExpMod.
Fail Module PolyExpTest : PolyExpType := PolyExpMod.

(* 11. NotSameConstructorNamesField - constructor names differ *)
Module Type ConsNamesType.
  Inductive I : Type := foo : I | bar : I.
End ConsNamesType.
Module ConsNamesMod.
  Inductive I : Type := baz : I | qux : I.
End ConsNamesMod.
Fail Module ConsNamesTest : ConsNamesType := ConsNamesMod.

(* 12. NotSameInductiveNameInBlockField - mutual inductive names differ *)
Module Type IndNamesType.
  Inductive A : Type := mkA : B -> A
  with B : Type := mkB : A -> B.
End IndNamesType.
Module IndNamesMod.
  Inductive A : Type := mkA : C -> A
  with C : Type := mkB : A -> C.
End IndNamesMod.
Fail Module IndNamesTest : IndNamesType := IndNamesMod.

(* 13. FiniteInductiveFieldExpected - expected inductive but got coinductive *)
Module Type FiniteType.
  Inductive I : Type := c : I.
End FiniteType.
Module FiniteMod.
  CoInductive I : Type := c : I.
End FiniteMod.
Fail Module FiniteTest : FiniteType := FiniteMod.

(* 14. InductiveNumbersFieldExpected - number of mutual inductives differs *)
Module Type NumIndType.
  Inductive I1 : Type := c1 : I1
  with I2 : Type := c2 : I2.
End NumIndType.
Module NumIndMod.
  Inductive I1 : Type := c1 : I1.
End NumIndMod.
Fail Module NumIndTest : NumIndType := NumIndMod.

(* 15. InductiveParamsNumberField - number of parameters differs *)
Module Type ParamsType.
  Inductive I (A B : Type) : Type := c : A -> B -> I A B.
End ParamsType.
Module ParamsMod.
  Inductive I (A : Type) : Type := c : A -> A -> I A.
End ParamsMod.
Fail Module ParamsTest : ParamsType := ParamsMod.

(* 16. RecordFieldExpected - expected record but got non-record *)
Module Type RecExpType.
  Record R := { field : nat }.
End RecExpType.
Module RecExpMod.
  Inductive R := Build_R : nat -> R.
End RecExpMod.
Fail Module RecExpTest : RecExpType := RecExpMod.

(* 17. RecordProjectionsExpected - projection names differ *)
Module Type RecProjType.
  Record R := { foo : nat; bar : bool }.
End RecProjType.
Module RecProjMod.
  Record R := { baz : nat; qux : bool }.
End RecProjMod.
Fail Module RecProjTest : RecProjType := RecProjMod.

(* 18. IncompatiblePolymorphism - polymorphic conversion generates constraints *)
Module Type IncompatPolyType.
  Polymorphic Definition f@{u} : Type@{u} -> Type@{u} := fun x => x.
End IncompatPolyType.
Module IncompatPolyMod.
  Polymorphic Definition f@{u v} : Type@{u} -> Type@{v} := fun x => x.
End IncompatPolyMod.
Fail Module IncompatPolyTest : IncompatPolyType := IncompatPolyMod.

(* 19. IncompatibleUnivConstraints - universe constraints incompatible *)
Module Type UnivConsType.
  Polymorphic Definition f@{u v|u < v} : Type@{u} := nat.
End UnivConsType.
Module UnivConsMod.
  Polymorphic Definition f@{u v|v < u} : Type@{u} := nat.
End UnivConsMod.
Fail Module UnivConsTest : UnivConsType := UnivConsMod.

(* 20. IncompatibleVariance - variance information incompatible
   Note: Variance subtyping is v1 <= v2 (module variance <= expected).
   Covariant (+) is more restrictive than Invariant (=).
   To trigger: module has Invariant but type expects Covariant. *)
Module Type VarianceType.
  Polymorphic Cumulative Inductive I@{+u} : Type@{u} := c : I.
End VarianceType.
Module VarianceMod.
  Polymorphic Cumulative Inductive I@{=u} : Type@{u} := c : I.
End VarianceMod.
Fail Module VarianceTest : VarianceType := VarianceMod.

(* NOTE: Some errors are not easily triggerable from this test file:
   - NoRewriteRulesSubtyping: requires -allow-rewrite-rules flag
   - NotEqualInductiveAliases: this error checks inductive aliasing through module resolvers;
     it may be dead code or only triggerable in very specific module functor contexts
   - IncompatibleUniverses in subtyping: tested above with Set/Type mismatch (Test4 in WithDefErrors)
   - IncompatibleQualities in subtyping: requires quality constraint conflicts during conversion
   - WithCannotConstrainPrimitive/Symbol: module types export primitives/symbols as Parameters,
     so "with Definition" finds a Parameter, not Primitive/Symbol *)

(* ========== with_constraint_error tests ========== *)

(* 22. WithTypeMismatch - type mismatch in with Definition *)
Module Type WithTypeType.
  Parameter x : nat.
End WithTypeType.
Fail Module Type WithTypeTest := WithTypeType with Definition x := true.

(* 23. WithBodyMismatch - body mismatch in with Definition *)
Module Type WithBodyType.
  Definition x := 5.
End WithBodyType.
Fail Module Type WithBodyTest := WithBodyType with Definition x := 10.

(* 24. WithUniverseMismatch - universe mismatch in with Definition *)
Module Type WithUnivType.
  Parameter x : Set.
End WithUnivType.
Definition big_type := Type.
Fail Module Type WithUnivTest := WithUnivType with Definition x := big_type.

(* 25. WithConstraintsMismatch - polymorphic binders mismatch *)
Module Type WithConsType.
  Polymorphic Parameter p@{u} : Type@{u}.
End WithConsType.
Fail Module Type WithConsTest := WithConsType with Definition p := nat.

(* 26. WithTypeMismatch with abstract type - test where expected type references module *)
Module Type WithAbsType.
  Parameter a : Type.
  Parameter b : a.
End WithAbsType.
Fail Module Type WithAbsTest := WithAbsType with Definition a := nat with Definition b := true.
