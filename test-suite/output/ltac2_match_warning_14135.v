Require Import Ltac2.Ltac2.

Ltac2 good_1(o: 'a option) :=
  match o with
  | Some x => 1
  | None => 2
  end.

Ltac2 good_2(o: 'a option) :=
  match o with
  | Some x => 1
  | _ => 2
  end.

Ltac2 redundant_constructor(o: 'a option) :=
  match o with
  | Some x => 1
  | None => 2
  | Some y => 3
  end.

Ltac2 redundant_catch_all(o: 'a option) :=
  match o with
  | Some x => 1
  | None => 2
  | _ => 3
  end.
