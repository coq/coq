Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Ltac2 Eval
  let nat := Option.get (Env.get [@Corelib; @Init; @Datatypes; @nat]) in
  let nat := match nat with
  | Std.IndRef nat => nat
  | _ => Control.throw Not_found
  end in
  let data := Ind.data nat in
  (* Check that there is only one inductive in the block *)
  let ntypes := Ind.nblocks data in
  let () := if Int.equal ntypes 1 then () else Control.throw Not_found in
  let nat' := Ind.repr (Ind.get_block data 0) in
  (* Check it corresponds *)
  let () := if Ind.equal nat nat' then () else Control.throw Not_found in
  let () := if Int.equal (Ind.index nat) 0 then () else Control.throw Not_found in
  (* Check the number of constructors *)
  let nconstr := Ind.nconstructors data in
  let () := if Int.equal nconstr 2 then () else Control.throw Not_found in
  (* Create a fresh instance *)
  let s := Ind.get_constructor data 1 in
  let s := Env.instantiate (Std.ConstructRef s) in
  constr:($s 0)
.
Print Acc.

Ltac2 Eval
  let acc := Option.get (Env.get [@Corelib; @Init; @Wf; @Acc]) in
  let acc := match acc with
  | Std.IndRef acc => acc
  | _ => Control.throw Not_found
  end in
  let data := Ind.data acc in
  let () :=
    if Int.equal (Ind.nparams data) 3 (* A, R, x are parameters. *)
    then () else Control.throw Not_found in
  let () :=
    if Int.equal (Ind.nparams_uniform data) 2 (* A, R are recursively uniform parameters. *)
    then () else Control.throw Not_found in
  let () :=
    if Int.equal (Array.get (Ind.constructor_nargs data) 0) 1
    then () else Control.throw Not_found in
  ()
.

Inductive ltac2_ind_test (A B: Type) (f : A -> B) (a : A) (b:= f a) : A -> B -> Type
  := c0 (a0 : A) (b0 := f a0) : ltac2_ind_test A B f a a0 b0.

Ltac2 Eval
  let acc := Option.get (Env.get [@ind; @ltac2_ind_test]) in
  let acc := match acc with
  | Std.IndRef acc => acc
  | _ => Control.throw Not_found
  end in
  let data := Ind.data acc in
  let () :=
    if Int.equal (Ind.nparams data) 4 (* A, B, f, a are parameters. *)
    then () else Control.throw Not_found in
  let () :=
    if Int.equal (Array.get (Ind.constructor_nargs data) 0) 1
                 (* a0 is the only argument of c0. *)
    then () else Control.throw Not_found in
  let () :=
    if Int.equal (Array.get (Ind.constructor_ndecls data) 0) 2
                 (* a0 and b0 can both be bound when pattern matching. *)
    then () else Control.throw Not_found in
  ()
.
