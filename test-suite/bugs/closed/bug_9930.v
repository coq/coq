Set Primitive Projections.
Record params := { width : nat }.
Definition p : params := Build_params 64.

Lemma foo : width p = 0 -> width p = 0.
  intros.
  let e := lazymatch type of H with ?e = 0 => e end in
  change tt with tt in H;
  let E := lazymatch type of H with ?E = 0 => E end in
  idtac "before:" e; idtac "after :" E;
  (* before: (width p) *)
  (* after : (width p) *)
  tryif constr_eq e E then exact H else idtac.
Qed.
