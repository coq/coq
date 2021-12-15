Axiom foo : Type.
Definition bar := 1.
Definition bar' := Eval cbv -[bar] in bar.
Declare Reduction red' := cbv -[bar].
Opaque bar.
Definition bar'' := Eval red' in bar.
Declare Reduction red'' := cbv -[bar]. (* Error: Cannot coerce bar to an
evaluable reference. *)
Definition bar''' := Eval cbv -[bar] in bar. (* Error: Cannot coerce bar to an
evaluable reference. *)
Definition foo' := Eval cbv -[foo] in foo. (* Error: Cannot coerce foo to an
evaluable reference. *)
