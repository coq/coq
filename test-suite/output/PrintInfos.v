(* coq-prog-args: ("-top" "PrintInfos") *)
About existT.
Print Term existT.
Print Implicit existT.

Print Term eq_refl.
About eq_refl.
Print Implicit eq_refl.

Print Term Nat.add.
About Nat.add.
Print Implicit Nat.add.

About plus_n_O.

Arguments le_S {n} [m] _.
Print Term le_S.

About comparison.
Print Term comparison.

Definition foo := forall x, x = 0.
Parameter bar : foo.

Arguments bar {x}.
About bar.
Print Term bar.

About Peano. (* Module *)
About sym_eq. (* Notation *)

Arguments eq_refl {A} {x}, {A} x.
Print Term eq_refl.


Definition newdef := fun x:nat => x.

Goal forall n:nat, n <> newdef n -> newdef n <> n -> False.
  intros n h h'.
  About n.                              (* search hypothesis *)
  About h.                              (* search hypothesis *)
Abort.

Goal forall n:nat, let g := newdef in n <> newdef n -> newdef n <> n -> False.
  intros n g h h'.
  About g.                              (* search hypothesis *)
  About h.                              (* search hypothesis *)
Abort.
