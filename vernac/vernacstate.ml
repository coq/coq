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
  lemmas  : Lemmas.t option;       (* proofs of lemmas currently opened *)
  shallow : bool                   (* is the state trimmed down (libstack) *)
}

let s_cache = ref None
let s_lemmas = ref None

let invalidate_cache () =
  s_cache := None;
  s_lemmas := None

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
    lemmas = !s_lemmas;
    shallow = false;
    parsing = Parser.cur_state ();
  }

let unfreeze_interp_state { system; lemmas; parsing } =
  do_if_not_cached s_cache States.unfreeze system;
  s_lemmas := lemmas;
  Pcoq.unfreeze parsing

let make_shallow st =
  let lib = States.lib_of_state st.system in
  { st with
    system = States.replace_lib st.system @@ Lib.drop_objects lib;
    shallow = true;
  }

(* Compatibility module *)
module Proof_global = struct

  let get () = !s_lemmas
  let set x = s_lemmas := x

  let freeze ~marshallable:_ = get ()
  let unfreeze x = s_lemmas := Some x

  exception NoCurrentProof

  let () =
    CErrors.register_handler begin function
      | NoCurrentProof ->
        CErrors.user_err Pp.(str "No focused proof (No proof-editing in progress).")
      | _ -> raise CErrors.Unhandled
    end

  open Proof_global
  open Lemmas

  let cc f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> f x

  let dd f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> s_lemmas := Some (f x)

  let there_are_pending_proofs () = !s_lemmas <> None
  let get_open_goals () = cc (pf_fold get_open_goals)

  let give_me_the_proof_opt () = Option.map (pf_fold give_me_the_proof) !s_lemmas
  let give_me_the_proof () = cc (pf_fold give_me_the_proof)
  let get_current_proof_name () = cc (pf_fold get_current_proof_name)

  let simple_with_current_proof f =
    dd (simple_with_current_proof f)

  type closed_proof = Proof_global.proof_object * Lemmas.proof_terminator

  let with_current_proof f =
    let pf, res = cc (with_current_proof f) in
    s_lemmas := Some pf; res

  let install_state s = s_lemmas := Some s

  let return_proof ?allow_partial () =
    cc (pf_fold (return_proof ?allow_partial))

  let close_future_proof ~opaque ~feedback_id pf =
    cc (fun pt -> pf_fold (fun st -> close_future_proof ~opaque ~feedback_id st pf) pt,
                  Internal.get_terminator pt)

  let close_proof ~opaque ~keep_body_ucst_separate f =
    cc (fun pt -> pf_fold ((close_proof ~opaque ~keep_body_ucst_separate f)) pt,
                  Internal.get_terminator pt)

  let discard_all () = s_lemmas := None
  let update_global_env () = dd (pf_map update_global_env)

  let get_current_context () = cc (pf_fold Pfedit.get_current_context)

  let get_all_proof_names () =
    try cc get_all_proof_names
    with NoCurrentProof -> []

  let copy_terminators ~src ~tgt =
    match src, tgt with
    | None, None -> None
    | Some _ , None -> None
    | None, Some x -> Some x
    | Some src, Some tgt -> Some (Internal.copy_terminators ~src ~tgt)

end
