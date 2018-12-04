
Set Printing Universes. Set Printing All.
Structure NoProof := no_proof { np_type : Type }.
Canonical Structure NP_Type := no_proof Type.
Check (fun np (T : np_type np) => Prop) _ Type.
