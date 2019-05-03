(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Parser = struct

  type state = Pcoq.frozen_t

  let init () = Pcoq.freeze ~marshallable:false

  let cur_state () = Pcoq.freeze ~marshallable:false

  let parse ps entry pa =
    Pcoq.unfreeze ps;
    Flags.with_option Flags.we_are_parsing (fun () ->
      try Pcoq.Entry.parse entry pa
      with e when CErrors.noncritical e ->
        let (e, info) = CErrors.push e in
        Exninfo.iraise (e, info))
    ()

end

type t = {
  parsing : Parser.state;
  system  : States.state;          (* summary + libstack *)
  proof   : Proof_global.t option; (* proof state *)
  shallow : bool                   (* is the state trimmed down (libstack) *)
}

let pstate st = Option.map Proof_global.get_current_pstate st.proof

let s_cache = ref None
let s_proof = ref None

let invalidate_cache () =
  s_cache := None;
  s_proof := None

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

let freeze_interp_state ~marshallable =
  { system = update_cache s_cache (States.freeze ~marshallable);
    proof  = !s_proof;
    shallow = false;
    parsing = Parser.cur_state ();
  }

let unfreeze_interp_state { system; proof; parsing } =
  do_if_not_cached s_cache States.unfreeze system;
  s_proof := proof;
  Pcoq.unfreeze parsing

let make_shallow st =
  let lib = States.lib_of_state st.system in
  { st with
    system = States.replace_lib st.system @@ Lib.drop_objects lib;
    shallow = true;
  }

(* Compatibility module *)
module Proof_global = struct

  let get () = !s_proof
  let set x = s_proof := x

  let freeze ~marshallable:_ = get ()
  let unfreeze x = s_proof := Some x

  exception NoCurrentProof

  let () =
    CErrors.register_handler begin function
      | NoCurrentProof ->
        CErrors.user_err Pp.(str "No focused proof (No proof-editing in progress).")
      | _ -> raise CErrors.Unhandled
    end

  open Proof_global

  let cc f = match !s_proof with
    | None -> raise NoCurrentProof
    | Some x -> f x

  let cc1 f = cc (fun p -> f (Proof_global.get_current_pstate p))

  let dd f = match !s_proof with
    | None -> raise NoCurrentProof
    | Some x -> s_proof := Some (f x)

  let dd1 f = dd (fun p -> Proof_global.modify_current_pstate f p)

  let there_are_pending_proofs () = !s_proof <> None
  let get_open_goals () = cc1 get_open_goals

  let set_terminator x = dd1 (set_terminator x)
  let give_me_the_proof_opt () = Option.map (fun p -> give_me_the_proof (Proof_global.get_current_pstate p)) !s_proof
  let give_me_the_proof () = cc1 give_me_the_proof
  let get_current_proof_name () = cc1 get_current_proof_name

  let simple_with_current_proof f =
    dd (simple_with_current_proof f)

  let with_current_proof f =
    let pf, res = cc (with_current_proof f) in
    s_proof := Some pf; res

  let install_state s = s_proof := Some s

  let return_proof ?allow_partial () =
    cc1 (return_proof ?allow_partial)

  let close_future_proof ~opaque ~feedback_id pf =
    cc1 (fun st -> close_future_proof ~opaque ~feedback_id st pf)

  let close_proof ~opaque ~keep_body_ucst_separate f =
    cc1 (close_proof ~opaque ~keep_body_ucst_separate f)

  let discard_all () = s_proof := None
  let update_global_env () = dd1 update_global_env

  let get_current_context () = cc1 Pfedit.get_current_context

  let get_all_proof_names () =
    try cc get_all_proof_names
    with NoCurrentProof -> []

  let copy_terminators ~src ~tgt =
    match src, tgt with
    | None, None -> None
    | Some _ , None -> None
    | None, Some x -> Some x
    | Some src, Some tgt -> Some (copy_terminators ~src ~tgt)

end
