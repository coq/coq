Inductive type := nat | bool.
Definition denote (t : type)
  := match t with
     | nat => Datatypes.nat
     | bool => Datatypes.bool
     end.
Ltac reify t :=
  lazymatch eval cbv beta in t with
  | Datatypes.nat => nat
  | Datatypes.bool => bool
  end.
Notation reify t := (ltac:(let rt := reify t in exact rt)) (only parsing).
Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).
Axiom Literal : forall {t}, denote t -> Type.
Declare Scope foo_scope.
Delimit Scope foo_scope with foo.
Open Scope foo_scope.
Section A.
  Notation "[ x ]" := (Literal (t:=reify_type_of x) x) (only parsing) : foo_scope.
  Check [1]. (* Literal 1 : Type *) (* as expected *)
  Notation "[ x ]" := (Literal x) : foo_scope.
  Check @Literal nat 1. (* Incorred: gives Literal 1 : Type when it should give [1]. Fixed by #12950 *)
  Notation "[ x ]" := (Literal (t:=reify_type_of x) x) (only parsing) : foo_scope.
  Check [1]. (* Incorrect: gives Literal 1 : Type when it should give [1]. This is disputable:
  #12950 considers that giving an only parsing a previous both-parsing-and-printing notation *)
End A.
Section B.
  Notation "[ x ]" := (Literal x) : foo_scope.
  Check @Literal nat 1. (* [1] : Type *)
  Fail Check [1]. (* As expected: The command has indeed failed with message:
  The term "1" has type "Datatypes.nat" while it is expected to have type
   "denote ?t". *)
  Notation "[ x ]" := (Literal (t:=reify_type_of x) x) (only parsing) : foo_scope.
  Check [1]. (* Should succeed, but instead fails with: Error:
  The term "1" has type "Datatypes.nat" while it is expected to have type
  "denote ?t". Fixed by #12950, but previous declaration is cancelled by #12950. *)
End B.
