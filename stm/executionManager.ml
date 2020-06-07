(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Scheduler

let log msg = Format.eprintf "@[%s@]@\n%!" msg

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

module SM = Map.Make (Stateid)

type execution_status =
  | Executing
  | Success of Vernacstate.t
  | Error of string Loc.located * Vernacstate.t (* State to use for resiliency *)

(* TODO store current sentence id for optimizations *)
type state = {
  initial : Vernacstate.t;
  cache : execution_status SM.t;
}

type progress_hook = state -> unit

let init vernac_state = {
    initial = vernac_state;
    cache = SM.empty;
  }

let execute st task =
  let base_vernac_st base_id =
    match base_id with
    | None -> st.initial
    | Some base_id ->
      begin match SM.find_opt base_id st.cache with
      | Some (Success vernac_st) -> vernac_st
      | Some (Error (_, vernac_st)) -> vernac_st (* Error resiliency *)
      | _ -> CErrors.anomaly Pp.(str "Missing state in cache (execute): " ++ Stateid.print base_id)
      end
  in
  match task with
  | base_id, Skip id ->
    let vernac_st = base_vernac_st base_id in
    { st with cache = SM.add id (Success vernac_st) st.cache }
  | base_id, Exec(id,ast) ->
    log @@ "Going to execute: " ^ Stateid.to_string id ^ " : " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
    let vernac_st = base_vernac_st base_id in
    begin try
      Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
      let vernac_st = Vernacinterp.interp ~st:vernac_st ast in (* TODO set status to "Executing" *)
      Sys.(set_signal sigint Signal_ignore);
      { st with cache = SM.add id (Success vernac_st) st.cache }
    with
    | Sys.Break as exn ->
      let exn = Exninfo.capture exn in
      Sys.(set_signal sigint Signal_ignore);
      Exninfo.iraise exn
    | any ->
      let (e, info) = Exninfo.capture any in
      Sys.(set_signal sigint Signal_ignore);
      let loc = Loc.get_loc info in
      let msg = CErrors.iprint (e, info) in
      { st with cache = SM.add id (Error ((loc, Pp.string_of_ppcmds msg), vernac_st)) st.cache }
    end
  | _ -> CErrors.anomaly Pp.(str "task not supported yet")

let observe progress_hook schedule id st =
  log @@ "Observe " ^ Stateid.to_string id;
  let rec build_tasks id tasks =
    begin match SM.find_opt id st.cache with
    | Some (Success vernac_st) ->
      (* We reached an already computed state *)
      log @@ "Reached computed state " ^ Stateid.to_string id;
      tasks
    | Some Executing -> CErrors.anomaly Pp.(str "depending on a state that is being executed")
    | Some (Error _) ->
      (* We try to be resilient to an error *)
      log @@ "Error resiliency on state " ^ Stateid.to_string id;
      tasks
    | None ->
      log @@ "Non-computed state " ^ Stateid.to_string id;
      let (base_id, task as todo) = task_for_sentence schedule id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        todo :: tasks
      | Some base_id ->
        build_tasks base_id (todo::tasks)
      end
    end
  in
  let tasks = build_tasks id [] in
  let interrupted = ref false in
  let execute st task =
    if !interrupted then st
    else try
      let st = execute st task in
      progress_hook st; st
    with Sys.Break -> (interrupted := true; st)
  in
  List.fold_left execute st tasks

let errors st =
  List.fold_left (fun acc (id, status) -> match status with Error ((loc,e),_st) -> (id,loc,e) :: acc | _ -> acc)
    [] @@ SM.bindings st.cache

let shift_locs st pos offset =
  let shift_error status = match status with
  | Error ((Some loc,e),st) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then Error ((Some (Loc.shift_loc offset offset loc),e),st)
    else if stop >= pos then Error ((Some (Loc.shift_loc 0 offset loc),e),st)
    else status
  | _ -> status
  in
  { st with cache = SM.map shift_error st.cache }

let executed_ids st =
  SM.fold (fun id status acc -> match status with Success _ | Error _ -> id :: acc | _ -> acc) st.cache []

let is_executed st id =
  match SM.find_opt id st.cache with
  | Some (Success _ | Error _) -> true
  | _ -> false

let query id st ast = assert false

let rec invalidate schedule id st =
  log @@ "Invalidating: " ^ Stateid.to_string id;
  let cache = SM.remove id st.cache in
  if cache == st.cache then st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (fun dep_id st -> invalidate schedule dep_id st) deps { st with cache }

let get_parsing_state_after st id =
  Option.bind (SM.find_opt id st.cache)
    (function Success st | Error (_,st) -> Some st.Vernacstate.parsing | _ -> None)

let get_proofview st id =
  match SM.find_opt id st.cache with
  | None -> log "Cannot find state for proofview"; None
  | Some Executing -> log "Proofview requested in state under execution"; None
  | Some (Error _) -> log "Proofview requested in error state"; None
  | Some (Success st) ->
    Vernacstate.unfreeze_interp_state st;
    try
      let newp = Vernacstate.Declare.give_me_the_proof () in
      Some (Proof.data newp)
    with Vernacstate.Declare.NoCurrentProof -> None
  [@@ocaml.warning "-3"];;
