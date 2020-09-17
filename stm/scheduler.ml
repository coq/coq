(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

let log msg = Format.eprintf "@[%s@]@\n%!" msg

type vernac_classification =
  ParsingEffect | StateEffect

let classify_vernac ast =
  let open Vernacextend in
  match Vernac_classifier.classify_vernac ast with
  | VtSideff (_, VtNow) -> ParsingEffect
  | _ -> StateEffect

module SM = Map.Make (Stateid)

(* TODO should we remove ASTs from here? *)
type task =
  | Skip of sentence_id
  | Exec of sentence_id * ast
  | OpaqueProof of sentence_id * sentence_id list
  | Query of sentence_id * ast
(*
  | SubProof of ast list
  | ModuleWithSignature of ast list
*)

type state = sentence_id list list
let initial_state = [[]]

type schedule = {
  tasks : (sentence_id option * task) SM.t;
  dependencies : Stateid.Set.t SM.t;
}

let initial_schedule = {
  tasks = SM.empty;
  dependencies = SM.empty;
}

let push_id id st =
  match st with l::q -> (id::l)::q | _ -> assert false

let base_id st = match st with (b::_)::_ -> Some b | _ -> None

let merge = function
  | [] -> assert false
  | l :: q ->
    match List.fold_left (fun st (id : sentence_id) -> push_id id st) q l with
    | l::q -> CList.uniquize l :: q
    | _ -> assert false

(* FIXME handle commands with side effects followed by `Abort` *)
let push_state id ast st =
  let open Vernacextend in
  match Vernac_classifier.classify_vernac ast with
  | VtStartProof _ -> base_id st, [id] :: push_id id st, Exec(id,ast)
  | VtQed (VtKeep (VtKeepAxiom | VtKeepOpaque)) ->
    let pop = List.tl st in
    base_id pop, push_id id pop, OpaqueProof(id, List.rev @@ List.hd st)
  | VtQed (VtKeep VtKeepDefined) ->
    base_id st, push_id id @@ merge st, Exec(id,ast)
  | (VtQuery | VtProofStep _) ->
    base_id st, push_id id st, Exec(id, ast)
  | VtSideff _ ->
    base_id st, List.map (fun s -> id :: s) st, Exec(id,ast)
  | _ -> assert false

(* For now, a trivial linear scheduler *)
let schedule_sentence (id,oast) st schedule =
  let base, st, task = match oast with
    | Some ast -> push_state id ast st
    | None -> base_id st, st, Skip id
  in
  log @@ "Scheduled " ^ (Stateid.to_string id) ^ " based on " ^ (match base with Some id -> Stateid.to_string id | None -> "no state");
  let tasks = SM.add id (base, task) schedule.tasks in
  let add_dep deps x id =
    let upd = function
    | Some deps -> Some (Stateid.Set.add id deps)
    | None -> Some (Stateid.Set.singleton id)
    in
    SM.update x upd deps
  in
  let dependencies =
    List.fold_left (fun deps l -> List.fold_left (fun deps x -> add_dep deps x id) deps l) schedule.dependencies st
  in
  st, { tasks; dependencies }

let task_for_sentence schedule id =
  match SM.find_opt id schedule.tasks with
  | Some x -> x
  | None -> CErrors.anomaly Pp.(str "cannot find schedule for sentence " ++ Stateid.print id)

let dependents schedule id =
  match SM.find_opt id schedule.dependencies with
  | Some x -> x
  | None -> CErrors.anomaly Pp.(str "cannot find dependents for sentence " ++ Stateid.print id)

(** Dependency computation algo *)
(*
{}
1. Definition y := ...
{{1}}
2. Lemma x : T.
{{},{1,2}}
3. Proof using v.
{{3},{1,2}}
4. tac1.
{{3,4},{1,2}}
5. Definition f := Type.
{{3,4,5},{1,2,5}}
6. Defined.    ||     6. Qed.
{{1,2,3,4,5,6}}  ||     {{1,2,5,6}}
7. Check x.
*)

let string_of_task (id,(base_id,task)) =
  let s = match task with
  | Skip id -> "Skip " ^ Stateid.to_string id
  | Exec (id, ast) -> "Exec " ^ Stateid.to_string id
  | OpaqueProof (id, ids) -> "OpaqueProof [" ^ Stateid.to_string id ^ " | " ^ String.concat "," (List.map Stateid.to_string ids) ^ "]"
  | Query(id,ast) -> "Query " ^ Stateid.to_string id
  in
  Format.sprintf "[%s] : [%s] -> %s" (Stateid.to_string id) (Option.cata Stateid.to_string "init" base_id) s

let string_of_schedule schedule =
  "Task\n" ^
  String.concat "\n" @@ List.map string_of_task @@ SM.bindings schedule.tasks
