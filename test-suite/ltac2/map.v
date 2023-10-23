Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].

Ltac2 ensure b := if b then () else Control.throw Regression_Test_Failure.

Ltac2 sort_int_list l :=
  FSet.elements
    (List.fold_left (fun acc x => FSet.add x acc) (FSet.empty FSet.Tags.int_tag) l).

Ltac2 Eval
  ensure (List.equal Int.equal [1;2;5;8] (sort_int_list [2;5;1;8])).

Ltac2 Eval
  ensure (FSet.is_empty (FSet.empty FSet.Tags.int_tag)).

Ltac2 Eval
  ensure (Bool.neg (FSet.is_empty (FSet.add "hello" (FSet.empty FSet.Tags.string_tag)))).

Ltac2 Eval
  ensure (FSet.is_empty (FSet.remove "hello" (FSet.add "hello" (FSet.empty FSet.Tags.string_tag)))).

Ltac2 Eval
  ensure (Bool.neg (FSet.is_empty (FSet.remove "hello" (FSet.add "other" (FSet.add "hello" (FSet.empty FSet.Tags.string_tag)))))).

Ltac2 Eval
  ensure (FSet.mem "other" (FSet.remove "hello" (FSet.add "other" (FSet.add "hello" (FSet.empty FSet.Tags.string_tag))))).

Ltac2 Eval
  ensure (Bool.neg (FSet.mem "hello" (FSet.remove "hello" (FSet.add "other" (FSet.add "hello" (FSet.empty FSet.Tags.string_tag)))))).

Ltac2 Notation "sprintf" fmt(format) := Message.Format.kfprintf (fun m => Message.to_string m) fmt.

Ltac2 Eval
  let m := FMap.empty FSet.Tags.string_tag in
  let m := FMap.add "one" 1 m in
  let m := FMap.add "two" 2 m in
  let m := FMap.add "three" 3 m in
  let m := FMap.add "four" 4 m in
  let m := FMap.mapi (fun s i => sprintf "%s=%i" s i) m in
  match FMap.find_opt "two" m with
  | None => ensure false
  | Some v => ensure (String.equal "two=2" v)
  end.

(* types didn't collapse *)
Fail Ltac2 Eval FSet.add 1 (FSet.empty FSet.Tags.string_tag).
