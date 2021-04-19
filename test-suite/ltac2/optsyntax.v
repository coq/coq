Require Import Ltac2.Ltac2.

Import Ltac2.Notations Ltac2.Control Ltac2.Printf Ltac2.Attributes.

Class A (n : nat).
Instance a0 : A 0 := {}.

Ltac2 parse_strategy tac opts :=
  let act value :=
    match Attribute.to_string value with
    | Some s =>
      if String.equal s "bfs" then Some Std.BFS
      else if String.equal s "dfs" then Some Std.DFS
      else unsupported_attribute_value tac "strategy" value
    | None =>
      unsupported_attribute_value tac "strategy" value
    end
  in parse_option opts "strategy" act.

Ltac2 parse_int_opt tac key opts :=
  let act value :=
    match Attribute.to_string value with
    | Some s =>
      match String.to_int s with
      | Some i => Some i
      | None => unsupported_attribute_value tac key value
      end
    | None =>
      unsupported_attribute_value tac key value
    end
  in parse_option opts key act.

Ltac2 tceauto_attributes opts :=
  let bfs := parse_flag opts "bfs" in
  let be := parse_flag opts "best_effort" in
  let strategy := parse_strategy "typeclasses eauto" opts in
  let depth := parse_int_opt "typeclasses eauto" "depth" opts in
  check_empty_attributes "typeclasses eauto" opts;
  (bfs, be, strategy, depth).

Ltac2 of_strategy s :=
  match s with
  | Some s =>
    match s with
    | Std.BFS => "breadth-first search"
    | Std.DFS => "depth-first search"
    end
  | None => "default"
  end.

Ltac2 of_depth d :=
  match d with
  | Some i => Message.of_int i
  | None => Message.of_string "∞"
  end.

Ltac2 rec of_list f l :=
  match l with
  | [] => Message.of_string "[]"
  | x :: xs => Message.concat (f x) (Message.concat (Message.of_string " :: ") (of_list f xs))
  end.

Ltac2 of_bfs_flag b := if b then Some Std.BFS else None.

Ltac2 tceauto (attrs : Attributes.t) (cstrs : constr list) (depth : int option) (dbs : ident list option) :=
  let (bfs, be, strat, _) := tceauto_attributes attrs in
  printf "cstrs: %a" (fun _ => of_list Message.of_constr) cstrs;
  printf "bfs: %a" (fun _ => Message.of_bool) bfs;
  printf "best_effort: %a" (fun _ => Message.of_bool) be;
  printf "strategy: %s" (of_strategy strat);
  printf "depth: %a" (fun _ => of_depth) depth;
  Std.typeclasses_eauto (of_bfs_flag bfs) depth dbs.

(* Probably ill-advised to use a constr list without delimiters but it works *)
Ltac2 Notation "tc" "eauto" attrs(attributes) cstrs(list0(constr, ",")) n(opt(tactic(0)))
  dbs(opt(seq("with", list1(ident)))) :=
  tceauto attrs cstrs n dbs.

(* A clearer alternative, but we still can't move "depth" to any position *)
Ltac2 Notation "tceauto'" attrs(attributes)
  cstrs(seq("[", list0(constr, ","), "]"))
  n(opt(seq("depth", "(", tactic(0), ")")))
  dbs(opt(seq("with", list1(ident)))) :=
  tceauto attrs cstrs n dbs.

Ltac2 tceauto_attrs (attrs : Attributes.t) (cstrs : constr list) (dbs : ident list option) :=
  let (bfs, be, strat, depth) := tceauto_attributes attrs in
  printf "cstrs: %a" (fun _ => of_list Message.of_constr) cstrs;
  printf "bfs: %a" (fun _ => Message.of_bool) bfs;
  printf "best_effort: %a" (fun _ => Message.of_bool) be;
  printf "strategy: %s" (of_strategy strat);
  printf "depth: %a" (fun _ => of_depth) depth;
  Std.typeclasses_eauto (of_bfs_flag bfs) depth dbs.

(* Use attributes for depth as well *)
Ltac2 Notation "tceauto_attrs" attrs(attributes)
  cstrs(seq("[", list0(constr, ","), "]"))
  dbs(opt(seq("with", list1(ident)))) :=
  tceauto_attrs attrs cstrs dbs.

Goal A 0.
Proof.
  (** Note the quite terrible I, 0 5*)
  tc eauto @[best_effort, strategy="dfs"] I, 0 5 with typeclass_instances.
  (* Parses and prints out as expected:
    cstrs: I :: 0 :: []
    bfs: false
    best_effort: true
    strategy: depth-first search
    depth: 5
  *)
  Undo 1.
  tceauto' @[best_effort, strategy="dfs"] [I, 0] depth(5) with typeclass_instances.
  (* Parses and prints out as expected:
    cstrs: I :: 0 :: []
    bfs: false
    best_effort: true
    strategy: depth-first search
    depth: 5
  *)
  Undo 1.
  Fail tceauto_attrs @[best_effort, depth="0", strategy="dfs"] [I, 0] with typeclass_instances.
  (* Invalid argument dept="0" *)
  Fail tceauto_attrs @[best_effort, dept="0", strategy="dfs"] [I, 0] with typeclass_instances.
  tceauto_attrs @[best_effort, strategy="dfs", depth="1"] [I, 0] with typeclass_instances.
Qed.
