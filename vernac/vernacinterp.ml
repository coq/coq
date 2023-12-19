(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr
open Synterp

let vernac_pperr_endline = CDebug.create ~name:"vernacinterp" ()

let interp_typed_vernac = Vernactypes.run

(* Timeout *)
let vernac_timeout ~timeout (f : 'a -> 'b) (x : 'a) : 'b =
  match Control.timeout timeout f x with
  | None -> Exninfo.iraise (Exninfo.capture CErrors.Timeout)
  | Some x -> x

(* Fail *)

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Loc.t option * Pp.t, unit) result =
  try
    let _ = f () in
    Error ()
  with
  (* Fail Timeout is a common pattern so we need to support it. *)
  | e ->
    (* The error has to be printed in the failing state *)
    let _, info as exn = Exninfo.capture e in
    if CErrors.is_anomaly e && e != CErrors.Timeout then Exninfo.iraise exn;
    Ok (Loc.get_loc info, CErrors.iprint exn)

let real_error_loc ~cmdloc ~eloc =
  if Loc.finer eloc cmdloc then eloc
  else cmdloc

(* We restore the state always *)
let with_fail ~loc ~st f =
  let res = with_fail f in
  Vernacstate.Interp.invalidate_cache ();
  Vernacstate.unfreeze_full_state st;
  match res with
  | Error () ->
    CErrors.user_err (Pp.str "The command has not failed!")
  | Ok (eloc, msg) ->
    let loc = if !Synterp.test_mode then real_error_loc ~cmdloc:loc ~eloc else None in
    if not !Flags.quiet || !Synterp.test_mode
    then Feedback.msg_notice ?loc Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg)

let with_succeed ~st f =
  let () = ignore (f ()) in
  Vernacstate.Interp.invalidate_cache ();
  Vernacstate.unfreeze_full_state st;
  if not !Flags.quiet
  then Feedback.msg_notice Pp.(str "The command has succeeded and its effects have been reverted.")

let locate_if_not_already ?loc (e, info) =
  (e, Option.cata (Loc.add_loc info) info (real_error_loc ~cmdloc:loc ~eloc:(Loc.get_loc info)))

let interp_control_entry ~loc (f : control_entry) ~st
    (fn : st:Vernacstate.t -> Vernacstate.LemmaStack.t option * Declare.OblState.t NeList.t) =
  match f with
  | ControlFail { st = synterp_st } ->
    with_fail ~loc ~st (fun () -> Vernacstate.Synterp.unfreeze synterp_st; fn ~st);
    st.Vernacstate.interp.lemmas, st.Vernacstate.interp.program
  | ControlSucceed { st = synterp_st } ->
    with_succeed ~st (fun () -> Vernacstate.Synterp.unfreeze synterp_st; fn ~st);
    st.Vernacstate.interp.lemmas, st.Vernacstate.interp.program
  | ControlTimeout { remaining } ->
    vernac_timeout ~timeout:remaining (fun () -> fn ~st) ()
  | ControlTime { synterp_duration } ->
    let result = System.measure_duration (fun () -> fn ~st) () in
    let result = Result.map (fun (v,d) -> v, System.duration_add d synterp_duration) result in
    Feedback.msg_notice @@ System.fmt_transaction_result result;
    begin match result with
    | Ok (v,_) -> v
    | Error (exn, _) -> Exninfo.iraise exn
    end
  | ControlInstructions { synterp_instructions } ->
    let result = System.count_instructions (fun () -> fn ~st) () in
    let result = Result.map (fun (v,d) -> v, System.instruction_count_add d synterp_instructions) result in
    Feedback.msg_notice @@ System.fmt_instructions_result result;
    begin match result with
    | Ok (v,_) -> v
    | Error (exn, _) -> Exninfo.iraise exn
    end
  | ControlRedirect s ->
    Topfmt.with_output_to_file s (fun () -> fn ~st) ()

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * loc is the Loc.t of the vernacular command being interpreted. *)
let rec interp_expr ?loc ~atts ~st c =
  match c with

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacSynPure VernacAbortAll    -> CErrors.user_err (Pp.str "AbortAll cannot be used through the Load command")
  | VernacSynPure VernacRestart     -> CErrors.user_err (Pp.str "Restart cannot be used through the Load command")
  | VernacSynPure VernacUndo _      -> CErrors.user_err (Pp.str "Undo cannot be used through the Load command")
  | VernacSynPure VernacUndoTo _    -> CErrors.user_err (Pp.str "UndoTo cannot be used through the Load command")

  (* Resetting *)
  | VernacSynPure VernacResetName _  -> CErrors.anomaly (Pp.str "VernacResetName not handled by Stm.")
  | VernacSynPure VernacResetInitial -> CErrors.anomaly (Pp.str "VernacResetInitial not handled by Stm.")
  | VernacSynPure VernacBack _       -> CErrors.anomaly (Pp.str "VernacBack not handled by Stm.")

  | VernacSynterp EVernacLoad (verbosely, fname) ->
    Attributes.unsupported_attributes atts;
    vernac_load ~verbosely fname

  | v ->
    let fv = Vernacentries.translate_vernac ?loc ~atts v in
    let stack = st.Vernacstate.interp.lemmas in
    let program = st.Vernacstate.interp.program in
    interp_typed_vernac ~pm:program ~stack fv

and vernac_load ~verbosely entries =
  (* Note that no proof should be open here, so the state here is just token for now *)
  let st = Vernacstate.freeze_full_state () in
  let v_mod = if verbosely then Flags.verbosely else Flags.silently in
  let interp_entry (stack, pm) (CAst.{ loc; v = cmd }, synterp_st) =
    Vernacstate.Synterp.unfreeze synterp_st;
    let st = Vernacstate.{ synterp = synterp_st; interp = { st.interp with Interp.lemmas = stack; program = pm }} in
    v_mod (interp_control ~st) (CAst.make ?loc cmd)
  in
  let pm = st.Vernacstate.interp.program in
  let stack = st.Vernacstate.interp.lemmas in
  let stack, pm =
    Dumpglob.with_glob_output Dumpglob.NoGlob
    (fun () -> List.fold_left interp_entry (stack, pm) entries) ()
  in
  (* If Load left a proof open, we fail too. *)
  if Option.has_some stack then
    CErrors.user_err Pp.(str "Files processed by Load cannot leave open proofs.");
  stack, pm

and interp_control ~st ({ CAst.v = cmd; loc }) =
  List.fold_right (fun flag fn -> interp_control_entry ~loc flag fn)
    cmd.control
    (fun ~st ->
       let before_univs = Global.universes () in
       let pstack, pm = with_generic_atts ~check:false cmd.attrs (fun ~atts ->
           interp_expr ?loc ~atts ~st cmd.expr)
       in
       let after_univs = Global.universes () in
       if before_univs == after_univs then pstack, pm
       else
         let f = Declare.Proof.update_sigma_univs after_univs in
         Option.map (Vernacstate.LemmaStack.map ~f) pstack, pm)
    ~st

(* XXX: This won't properly set the proof mode, as of today, it is
   controlled by the STM. Thus, we would need access information from
   the classifier. The proper fix is to move it to the STM, however,
   the way the proof mode is set there makes the task non trivial
   without a considerable amount of refactoring.
*)

(* Interpreting a possibly delayed proof *)
let interp_qed_delayed ~proof ~st pe =
  let stack = st.Vernacstate.interp.lemmas in
  let pm = st.Vernacstate.interp.program in
  let stack = Option.cata (fun stack -> snd @@ Vernacstate.LemmaStack.pop stack) None stack in
  let pm = NeList.map_head (fun pm -> match pe with
      | Admitted ->
        Declare.Proof.save_lemma_admitted_delayed ~pm ~proof
      | Proved (_,idopt) ->
        let pm, _ = Declare.Proof.save_lemma_proved_delayed ~pm ~proof ~idopt in
        pm)
      pm
  in
  stack, pm

let interp_qed_delayed_control ~proof ~st ~control { CAst.loc; v=pe } =
  List.fold_right (fun flag fn -> interp_control_entry ~loc flag fn)
    control
    (fun ~st -> interp_qed_delayed ~proof ~st pe)
    ~st

(* General interp with management of state *)

(* Be careful with the cache here in case of an exception. *)
let interp_gen ~verbosely ~st ~interp_fn cmd =
  try
    let v_mod = if verbosely then Flags.verbosely else Flags.silently in
    let ontop = v_mod (interp_fn ~st) cmd in
    Vernacstate.Declare.set ontop [@ocaml.warning "-3"];
    Vernacstate.Interp.freeze_interp_state ()
  with exn ->
    let exn = Exninfo.capture exn in
    let exn = locate_if_not_already ?loc:cmd.CAst.loc exn in
    Vernacstate.Interp.invalidate_cache ();
    Exninfo.iraise exn

(* Regular interp *)
let interp ?(verbosely=true) ~st cmd =
  Vernacstate.unfreeze_full_state st;
  vernac_pperr_endline Pp.(fun () -> str "interpreting: " ++ Ppvernac.pr_vernac_expr cmd.CAst.v.expr);
  let entry = NewProfile.profile "synterp" (fun () -> Synterp.synterp_control cmd) () in
  let interp = NewProfile.profile "interp" (fun () -> interp_gen ~verbosely ~st ~interp_fn:interp_control entry) () in
  Vernacstate.{ synterp = Vernacstate.Synterp.freeze (); interp }

let interp_entry ?(verbosely=true) ~st entry =
  Vernacstate.unfreeze_full_state st;
  interp_gen ~verbosely ~st ~interp_fn:interp_control entry

let interp_qed_delayed_proof ~proof ~st ~control (CAst.{loc; v = pe } as e) : Vernacstate.Interp.t =
  let cmd = CAst.make ?loc { control; expr = VernacSynPure (VernacEndProof pe); attrs = [] } in
  let CAst.{ loc; v = entry } = Synterp.synterp_control cmd in
  let control = entry.control in
  NewProfile.profile "interp-delayed-qed" (fun () ->
      interp_gen ~verbosely:false ~st
        ~interp_fn:(interp_qed_delayed_control ~proof ~control) e)
    ()
