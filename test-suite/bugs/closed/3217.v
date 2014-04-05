(** [Set Implicit Arguments] causes Coq to run out of memory on [Qed] before c3feef4ed5dec126f1144dec91eee9c0f0522a94 *)
Set Implicit Arguments.

Variable LEM: forall P : Prop, sumbool P (P -> False).

Definition pmap := option (nat -> option nat).

Definition pmplus (oha ohb: pmap) : pmap :=
 match oha, ohb with
 | Some ha, Some hb =>
   if LEM (oha = ohb) then None else None
 | _, _ => None
 end.

Definition pmemp: pmap := Some (fun _ => None).

Lemma foo:
 True ->
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
    (pmplus pmemp
     pmemp))))))))))))
    =
    None -> True.
Proof.
  auto.
Timeout 2 Qed.
