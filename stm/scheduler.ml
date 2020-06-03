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

module SM = Map.Make (Stateid)

type task =
  | Skip of sentence_id
  | Exec of sentence_id * ast
  | DelegateOpaqueProof of {
      proof_script: sentence_id * ast list;
      section_info: string list;
    }
  | DelegateQuery of sentence_id * ast
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

(* For now, a trivial linear scheduler *)
let schedule_sentence (id,oast) st schedule =
  let base = match st with (b::_)::_ -> Some b | _ -> None in
  log @@ "Scheduled " ^ (Stateid.to_string id) ^ " based on " ^ (match base with Some id -> Stateid.to_string id | None -> "no state");
  let st = match st with l::q -> (id::l)::q | _ -> assert false in
  let task = match oast with Some ast -> Exec(id, ast) | None -> Skip id in
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
{{2},{1}}
3. Proof using v.
{{2,3},{1}}
4. tac1.
{{2,3,4},{1}}
5. abstract tac2.
{{2,3,4,5},{1,5}}
6. Defined.
{{1,2,3,5}}

*)
