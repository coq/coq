Require Import Ltac2.Ltac2.

Ltac2 Type exn ::= [ Regression_Test_Failure ].

Ltac2 ensure b := if b then () else Control.throw Regression_Test_Failure.

Ltac2 sort_int_list l :=
  Int.FSet.elements
    (List.fold_left (fun acc x => Int.FSet.add x acc) l (Int.FSet.empty ())).

Ltac2 Eval
  ensure (List.equal Int.equal [1;2;5;8] (sort_int_list [2;5;1;8])).

Ltac2 Eval
  ensure (String.FSet.is_empty (String.FSet.empty ())).

Ltac2 Eval
  ensure (Bool.neg (String.FSet.is_empty (String.FSet.add "hello" (String.FSet.empty ())))).

Ltac2 Eval
  ensure (String.FSet.is_empty (String.FSet.remove "hello" (String.FSet.add "hello" (String.FSet.empty ())))).

Ltac2 Eval
  ensure (Bool.neg (String.FSet.is_empty (String.FSet.remove "hello" (String.FSet.add "other" (String.FSet.add "hello" (String.FSet.empty ())))))).

Ltac2 Eval
  ensure (String.FSet.mem "other" (String.FSet.remove "hello" (String.FSet.add "other" (String.FSet.add "hello" (String.FSet.empty ()))))).

Ltac2 Eval
  ensure (Bool.neg (String.FSet.mem "hello" (String.FSet.remove "hello" (String.FSet.add "other" (String.FSet.add "hello" (String.FSet.empty ())))))).

Ltac2 Notation "sprintf" fmt(format) := Message.Format.kfprintf (fun m => Message.to_string m) fmt.

Ltac2 Eval
  let m := String.Map.empty () in
  let m := String.Map.add "one" 1 m in
  let m := String.Map.add "two" 2 m in
  let m := String.Map.add "three" 3 m in
  let m := String.Map.add "four" 4 m in
  let m := String.Map.mapi (fun s i => sprintf "%s=%i" s i) m in
  match String.Map.find_opt "two" m with
  | None => ensure false
  | Some v => ensure (String.equal "two=2" v)
  end.

(* types didn't collapse *)
Fail Ltac2 Eval
  ensure (Int.FSet.is_empty (String.FSet.empty ())).
