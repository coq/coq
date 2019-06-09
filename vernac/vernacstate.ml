(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

module LemmaStack = struct

  type t = Lemmas.t * Lemmas.t list

  let map f (pf, pfl) = (f pf, List.map f pfl)

  let map_top_pstate ~f (pf, pfl) = (Lemmas.pf_map f pf, pfl)

  let pop (ps, p) = match p with
    | [] -> ps, None
    | pp :: p -> ps, Some (pp, p)

  let with_top (p, _) ~f = f p
  let with_top_pstate (p, _) ~f = Lemmas.pf_fold f p

  let push ontop a =
    match ontop with
    | None -> a , []
    | Some (l,ls) -> a, (l :: ls)

  let get_all_proof_names (pf : t) =
    let prj x = Lemmas.pf_fold Proof_global.get_proof x in
    let (pn, pns) = map Proof.(function pf -> (data (prj pf)).name) pf in
    pn :: pns

  let copy_info src tgt =
    Lemmas.pf_map (fun _ -> Lemmas.pf_fold (fun x -> x) tgt) src

  let copy_info ~src ~tgt =
    let (ps, psl), (ts,tsl) = src, tgt in
    copy_info ps ts,
    List.map2 (fun op p -> copy_info op p) psl tsl

end

type t = {
  parsing : Parser.state;
  system  : States.state;          (* summary + libstack *)
  lemmas  : LemmaStack.t option;   (* proofs of lemmas currently opened *)
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

  let get_pstate () =
    Option.map (LemmaStack.with_top ~f:(Lemmas.pf_fold (fun x -> x))) !s_lemmas

  let freeze ~marshallable:_ = get ()
  let unfreeze x = s_lemmas := Some x

  exception NoCurrentProof

  let () =
    CErrors.register_handler begin function
      | NoCurrentProof ->
        CErrors.user_err Pp.(str "No focused proof (No proof-editing in progress).")
      | _ -> raise CErrors.Unhandled
    end

  open Lemmas
  open Proof_global

  let cc f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> LemmaStack.with_top_pstate ~f x

  let cc_lemma f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> LemmaStack.with_top ~f x

  let cc_stack f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> f x

  let dd f = match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some x -> s_lemmas := Some (LemmaStack.map_top_pstate ~f x)

  let there_are_pending_proofs () = !s_lemmas <> None
  let get_open_goals () = cc get_open_goals

  let give_me_the_proof_opt () = Option.map (LemmaStack.with_top_pstate ~f:get_proof) !s_lemmas
  let give_me_the_proof () = cc get_proof
  let get_current_proof_name () = cc get_proof_name

  let map_proof f = dd (map_proof f)
  let with_current_proof f =
    match !s_lemmas with
    | None -> raise NoCurrentProof
    | Some stack ->
      let pf, res = LemmaStack.with_top_pstate stack ~f:(map_fold_proof_endline f) in
      let stack = LemmaStack.map_top_pstate stack ~f:(fun _ -> pf) in
      s_lemmas := Some stack;
      res

  type closed_proof = Proof_global.proof_object * Lemmas.Info.t


  let return_proof ?allow_partial () = cc (return_proof ?allow_partial)

  let close_future_proof ~opaque ~feedback_id pf =
    cc_lemma (fun pt -> pf_fold (fun st -> close_future_proof ~opaque ~feedback_id st pf) pt,
                        Internal.get_info pt)

  let close_proof ~opaque ~keep_body_ucst_separate f =
    cc_lemma (fun pt -> pf_fold ((close_proof ~opaque ~keep_body_ucst_separate f)) pt,
                        Internal.get_info pt)

  let discard_all () = s_lemmas := None
  let update_global_env () = dd (update_global_env)

  let get_current_context () = cc Pfedit.get_current_context

  let get_all_proof_names () =
    try cc_stack LemmaStack.get_all_proof_names
    with NoCurrentProof -> []

  let copy_terminators ~src ~tgt =
    match src, tgt with
    | None, None -> None
    | Some _ , None -> None
    | None, Some x -> Some x
    | Some src, Some tgt -> Some (LemmaStack.copy_info ~src ~tgt)

end
