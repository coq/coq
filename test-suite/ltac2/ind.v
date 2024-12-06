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
