(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Goptions

module Dyn = Dyn.Make()

module DMap = Dyn.Map(struct type 'a t = 'a -> unit Proofview.tactic end)

let interp_map = ref DMap.empty

type interpretable = I : 'a Dyn.tag * 'a -> interpretable
type 'a tactic_interpreter = Interpreter of ('a -> interpretable)

let register_tactic_interpreter na f =
  let t = Dyn.create na in
  interp_map := DMap.add t f !interp_map;
  Interpreter (fun x -> I (t,x))

let interp_tac (I (tag,t)) =
  let f = DMap.find tag !interp_map in
  f t

type parallel_solver =
  pstate:Declare.Proof.t ->
  info:int option ->
  interpretable ->
  abstract:bool ->
  with_end_tac:bool ->
  Declare.Proof.t

let { Goptions.get = print_info_trace } =
  declare_intopt_option_and_ref
    ~key:["Info" ; "Level"]
    ~value:None
    ()

let solve_core ~pstate n ~info t ~with_end_tac:b =
  let pstate, status = Declare.Proof.map_fold_endline ~f:(fun etac p ->
      let with_end_tac = if b then Some etac else None in
      let info = Option.append info (print_info_trace ()) in
      let (p,status) = Proof.solve n info t ?with_end_tac p in
      (* in case a strict subtree was completed,
         go back to the top of the prooftree *)
      let p = Proof.maximal_unfocus Vernacentries.command_focus p in
      p,status) pstate in
  if not status then Feedback.feedback Feedback.AddedAxiom;
  pstate

let solve ~pstate n ~info t ~with_end_tac =
  let t = interp_tac t in
  solve_core ~pstate n ~info t ~with_end_tac

let check_par_applicable pstate =
  Declare.Proof.fold pstate ~f:(fun p ->
    (Proof.data p).Proof.goals |> List.iter (fun goal ->
    let is_ground =
      let { Proof.sigma = sigma0 } = Declare.Proof.fold pstate ~f:Proof.data in
      let g = Evd.find_undefined sigma0 goal in
      let concl, hyps = Evd.evar_concl g, Evd.evar_context g in
      Evarutil.is_ground_term sigma0 concl &&
      List.for_all (Context.Named.Declaration.for_all (Evarutil.is_ground_term sigma0)) hyps in
    if not is_ground then
      CErrors.user_err
        Pp.(strbrk("The par: goal selector does not support goals with existential variables"))))

let par_implementation = ref (fun ~pstate ~info t ~abstract ~with_end_tac ->
  let t = interp_tac t in
  let t = Proofview.Goal.enter (fun _ ->
    if abstract then Abstract.tclABSTRACT None ~opaque:true t else t) 
  in
  solve_core ~pstate Goal_select.SelectAll ~info t ~with_end_tac)

let set_par_implementation f = par_implementation := f

let solve_parallel ~pstate ~info t ~abstract ~with_end_tac =
  check_par_applicable pstate;
  !par_implementation ~pstate ~info t ~abstract ~with_end_tac
