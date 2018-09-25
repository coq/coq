(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  system  : States.state;          (* summary + libstack *)
  proof   : Proof_global.t option; (* proof state *)
  shallow : bool                   (* is the state trimmed down (libstack) *)
}

let s_cache = ref None

let invalidate_cache () =
  s_cache := None

let update_cache rf v =
  rf := Some v; v

let do_if_not_cached rf f v =
  match !rf with
  | None ->
    rf := Some v; f v
  | Some vc when vc != v ->
    rf := Some v; f v
  | Some _ ->
    ()

let freeze_interp_state ~pstate marshallable =
  { system = update_cache s_cache (States.freeze ~marshallable);
    proof  = pstate;
    shallow = marshallable = `Shallow }

let unfreeze_interp_state { system } =
  do_if_not_cached s_cache States.unfreeze system

exception HasNotFailed
exception HasFailed of Pp.t

(* XXX STATE: this type hints that restoring the state should be the
   caller's responsibility *)
let with_fail ~st f =
  try
    (* If the command actually works, ignore its effects on the state.
     * Note that error has to be printed in the right state, hence
     * within the purified function *)
    try
      ignore (f ());
      raise HasNotFailed
    with
    | HasNotFailed as e -> raise e
    | e ->
      let e = CErrors.push e in
      raise (HasFailed
               (CErrors.iprint
                  (ExplainErr.process_vernac_interp_error ~allow_uncaught:false e)))
  with e when CErrors.noncritical e ->
    (* Restore the previous state XXX Careful here with the cache! *)
    invalidate_cache ();
    unfreeze_interp_state st;
    let (e, _) = CErrors.push e in
    match e with
    | HasNotFailed ->
      CErrors.user_err ~hdr:"Fail" Pp.(str "The command has not failed!")
    | HasFailed msg ->
      if not !Flags.quiet || !Flags.test_mode then Feedback.msg_info
          Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg);
      st.proof
    | _ -> assert false

module StmCompat = struct

  let p_state = ref None

  let freeze marshallable =
  { system = update_cache s_cache (States.freeze ~marshallable);
    proof  = !p_state;
    shallow = marshallable = `Shallow }

  let unfreeze { system ; proof } =
    do_if_not_cached s_cache States.unfreeze system;
    p_state := proof

  let with_fail ~(st : t) f =
    let f () = f (); !p_state in
    p_state := with_fail ~st f

  exception NoCurrentProof

  let there_are_pending_proofs () =
    not Option.(is_empty !p_state)

  let get_open_goals () =
    Option.cata Proof_global.get_open_goals 0 !p_state

  let set_terminator t =
    p_state := Option.map Proof_global.(set_terminator t) !p_state

  let give_me_the_proof () =
    match !p_state with
    | Some pstate -> Proof_global.give_me_the_proof pstate
    | None -> raise NoCurrentProof

  let get_current_proof_name () =
    match !p_state with
    | Some pstate -> Proof_global.get_current_proof_name pstate
    | None -> raise NoCurrentProof

  let simple_with_current_proof f =
    p_state :=
      match !p_state with
      | Some pstate -> Some (Proof_global.simple_with_current_proof f pstate)
      | None -> raise NoCurrentProof

  let with_current_proof f =
    let ps, ret =
      match !p_state with
      | Some pstate -> Proof_global.with_current_proof f pstate
      | None -> raise NoCurrentProof
    in
    p_state := Some ps; ret

  let install_state st = p_state := Some st

  let return_proof ?allow_partial () =
    match !p_state with
    | Some pstate ->
      Proof_global.return_proof ?allow_partial pstate
    | None -> raise NoCurrentProof

  let close_future_proof ~feedback_id f =
    match !p_state with
    | Some pstate ->
      Proof_global.close_future_proof ~feedback_id pstate f
    | None -> raise NoCurrentProof

  let close_proof ~keep_body_ucst_separate f =
    match !p_state with
    | Some pstate ->
      Proof_global.close_proof ~keep_body_ucst_separate f pstate
    | None -> raise NoCurrentProof

  let discard_all () = ()
  let update_global_env () = ()

  let get_current_context () =
    match !p_state with
    | Some pstate ->
      Pfedit.get_current_context pstate
    | None ->
      let env = Global.env () in
      Evd.from_env env, env

end
