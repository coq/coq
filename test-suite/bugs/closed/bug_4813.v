(* On the strength of "apply with" (see also #4782) *)

Record ProverT := { Facts : Type }.
Record ProverT_correct (P : ProverT) :=  { Valid : Facts P -> Prop ;
                                           Valid_weaken : Valid = Valid }.
Definition reflexivityValid (_ : unit) := True.
Definition reflexivityProver_correct : ProverT_correct {| Facts := unit |}.
Proof.
    eapply Build_ProverT_correct with (Valid := reflexivityValid).
