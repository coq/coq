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

(* XXX Should move to a common library *)
let debug = false
let vernac_pperr_endline pp =
  if debug then Format.eprintf "@[%a@]@\n%!" Pp.pp_with (pp ()) else ()

(* EJGA: We may remove this, only used twice below *)
let vernac_require_open_lemma ~stack f =
  match stack with
  | Some stack -> f stack
  | None ->
    CErrors.user_err (Pp.str "Command not supported (No proof-editing in progress)")

let interp_typed_vernac c ~stack =
  let open Vernacextend in
  match c with
  | VtDefault f -> f (); stack
  | VtNoProof f ->
    if Option.has_some stack then
      CErrors.user_err (Pp.str "Command not supported (Open proofs remain)");
    let () = f () in
    stack
  | VtCloseProof f ->
    vernac_require_open_lemma ~stack (fun stack ->
        let lemma, stack = Vernacstate.LemmaStack.pop stack in
        f ~lemma;
        stack)
  | VtOpenProof f ->
    Some (Vernacstate.LemmaStack.push stack (f ()))
  | VtModifyProof f ->
    Option.map (Vernacstate.LemmaStack.map_top_pstate ~f:(fun pstate -> f ~pstate)) stack
  | VtReadProofOpt f ->
    let pstate = Option.map (Vernacstate.LemmaStack.with_top_pstate ~f:(fun x -> x)) stack in
    f ~pstate;
    stack
  | VtReadProof f ->
    vernac_require_open_lemma ~stack
      (Vernacstate.LemmaStack.with_top_pstate ~f:(fun pstate -> f ~pstate));
    stack

(* Default proof mode, to be set at the beginning of proofs for
   programs that cannot be statically classified. *)
let proof_mode_opt_name = ["Default";"Proof";"Mode"]

let get_default_proof_mode =
  Goptions.declare_interpreted_string_option_and_ref
    ~depr:false
    ~key:proof_mode_opt_name
    ~value:(Pvernac.register_proof_mode "Noedit" Pvernac.Vernac_.noedit_mode)
    (fun name -> match Pvernac.lookup_proof_mode name with
    | Some pm -> pm
    | None -> CErrors.user_err Pp.(str (Format.sprintf "No proof mode named \"%s\"." name)))
    Pvernac.proof_mode_to_string

(** A global default timeout, controlled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let default_timeout = ref None

(* Timeout *)
let vernac_timeout ?timeout (f : 'a -> 'b) (x : 'a) : 'b =
  match !default_timeout, timeout with
  | _, Some n
  | Some n, None ->
    Control.timeout n f x CErrors.Timeout
  | None, None ->
    f x

(* Fail *)
let test_mode = ref false

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Pp.t, unit) result =
  try
    let _ = f () in
    Error ()
  with
  (* Fail Timeout is a common pattern so we need to support it. *)
  | e when CErrors.noncritical e || e = CErrors.Timeout ->
    (* The error has to be printed in the failing state *)
    Ok CErrors.(iprint (Exninfo.capture e))

(* We restore the state always *)
let with_fail ~st f =
  let res = with_fail f in
  Vernacstate.invalidate_cache ();
  Vernacstate.unfreeze_interp_state st;
  match res with
  | Error () ->
    CErrors.user_err ~hdr:"Fail" (Pp.str "The command has not failed!")
  | Ok msg ->
    if not !Flags.quiet || !test_mode
    then Feedback.msg_notice Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg)

let locate_if_not_already ?loc (e, info) =
  match Loc.get_loc info with
  | None   -> (e, Option.cata (Loc.add_loc info) info loc)
  | Some l -> (e, info)

let mk_time_header =
  (* Drop the time header to print the command, we should indeed use a
     different mechanism to `-time` commands than the current hack of
     adding a time control to the AST. *)
  let pr_time_header vernac =
    let vernac = match vernac with
      | { CAst.v = { control = ControlTime _ :: control; attrs; expr }; loc } ->
        CAst.make ?loc { control; attrs; expr }
      | _ -> vernac
    in
    Topfmt.pr_cmd_header vernac
  in
  fun vernac -> Lazy.from_fun (fun () -> pr_time_header vernac)

let interp_control_flag ~time_header (f : control_flag) ~st
    (fn : st:Vernacstate.t -> Vernacstate.LemmaStack.t option) =
  match f with
  | ControlFail ->
    with_fail ~st (fun () -> fn ~st);
    st.Vernacstate.lemmas
  | ControlTimeout timeout ->
    vernac_timeout ~timeout (fun () -> fn ~st) ()
  | ControlTime batch ->
    let header = if batch then Lazy.force time_header  else Pp.mt () in
    System.with_time ~batch ~header (fun () -> fn ~st) ()
  | ControlRedirect s ->
    Topfmt.with_output_to_file s (fun () -> fn ~st) ()

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * loc is the Loc.t of the vernacular command being interpreted. *)
let rec interp_expr ~atts ~st c =
  let stack = st.Vernacstate.lemmas in
  vernac_pperr_endline Pp.(fun () -> str "interpreting: " ++ Ppvernac.pr_vernac_expr c);
  match c with

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacAbortAll    -> CErrors.user_err (Pp.str "AbortAll cannot be used through the Load command")
  | VernacRestart     -> CErrors.user_err (Pp.str "Restart cannot be used through the Load command")
  | VernacUndo _      -> CErrors.user_err (Pp.str "Undo cannot be used through the Load command")
  | VernacUndoTo _    -> CErrors.user_err (Pp.str "UndoTo cannot be used through the Load command")

  (* Resetting *)
  | VernacResetName _  -> CErrors.anomaly (Pp.str "VernacResetName not handled by Stm.")
  | VernacResetInitial -> CErrors.anomaly (Pp.str "VernacResetInitial not handled by Stm.")
  | VernacBack _       -> CErrors.anomaly (Pp.str "VernacBack not handled by Stm.")

  (* This one is possible to handle here *)
  | VernacAbort id    -> CErrors.user_err (Pp.str "Abort cannot be used through the Load command")
  | VernacLoad (verbosely, fname) ->
    Attributes.unsupported_attributes atts;
    vernac_load ~verbosely fname
  | v ->
    let fv = Vernacentries.translate_vernac ~atts v in
    interp_typed_vernac ~stack fv

and vernac_load ~verbosely fname =
  let exception End_of_input in

  (* Note that no proof should be open here, so the state here is just token for now *)
  let st = Vernacstate.freeze_interp_state ~marshallable:false in
  let fname =
    Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (Pp.str x)) fname in
  let fname = CUnix.make_suffix fname ".v" in
  let input =
    let longfname = Loadpath.locate_file fname in
    let in_chan = Util.open_utf8_file_in longfname in
    Pcoq.Parsable.make ~loc:(Loc.initial (Loc.InFile longfname)) (Stream.of_channel in_chan) in
  (* Parsing loop *)
  let v_mod = if verbosely then Flags.verbosely else Flags.silently in
  let parse_sentence proof_mode = Flags.with_option Flags.we_are_parsing
      (fun po ->
         match Pcoq.Entry.parse (Pvernac.main_entry proof_mode) po with
         | Some x -> x
         | None -> raise End_of_input) in
  let rec load_loop ~stack =
    try
      let proof_mode = Option.map (fun _ -> get_default_proof_mode ()) stack in
      let stack =
        v_mod (interp_control ~st:{ st with Vernacstate.lemmas = stack })
          (parse_sentence proof_mode input) in
      load_loop ~stack
    with
      End_of_input ->
      stack
  in
  let stack = load_loop ~stack:st.Vernacstate.lemmas in
  (* If Load left a proof open, we fail too. *)
  if Option.has_some stack then
    CErrors.user_err Pp.(str "Files processed by Load cannot leave open proofs.");
  stack

and interp_control ~st ({ CAst.v = cmd } as vernac) =
  let time_header = mk_time_header vernac in
  List.fold_right (fun flag fn -> interp_control_flag ~time_header flag fn)
    cmd.control
    (fun ~st ->
       let before_univs = Global.universes () in
       let pstack = interp_expr ~atts:cmd.attrs ~st cmd.expr in
       if before_univs == Global.universes () then pstack
       else Option.map (Vernacstate.LemmaStack.map_top_pstate ~f:Declare.Proof.update_global_env) pstack)
    ~st

(* XXX: This won't properly set the proof mode, as of today, it is
   controlled by the STM. Thus, we would need access information from
   the classifier. The proper fix is to move it to the STM, however,
   the way the proof mode is set there makes the task non trivial
   without a considerable amount of refactoring.
*)

(* Interpreting a possibly delayed proof *)
let interp_qed_delayed ~proof ~info ~st pe : Vernacstate.LemmaStack.t option =
  let stack = st.Vernacstate.lemmas in
  let stack = Option.cata (fun stack -> snd @@ Vernacstate.LemmaStack.pop stack) None stack in
  let () = match pe with
    | Admitted ->
      Declare.save_lemma_admitted_delayed ~proof ~info
    | Proved (_,idopt) ->
      Declare.save_lemma_proved_delayed ~proof ~info ~idopt in
  stack

let interp_qed_delayed_control ~proof ~info ~st ~control { CAst.loc; v=pe } =
  let time_header = mk_time_header (CAst.make ?loc { control; attrs = []; expr = VernacEndProof pe }) in
  List.fold_right (fun flag fn -> interp_control_flag ~time_header flag fn)
    control
    (fun ~st -> interp_qed_delayed ~proof ~info ~st pe)
    ~st

(* General interp with management of state *)
let () = let open Goptions in
  declare_int_option
    { optdepr  = false;
      optkey   = ["Default";"Timeout"];
      optread  = (fun () -> !default_timeout);
      optwrite = ((:=) default_timeout) }

(* Be careful with the cache here in case of an exception. *)
let interp_gen ~verbosely ~st ~interp_fn cmd =
  Vernacstate.unfreeze_interp_state st;
  try vernac_timeout (fun st ->
      let v_mod = if verbosely then Flags.verbosely else Flags.silently in
      let ontop = v_mod (interp_fn ~st) cmd in
      Vernacstate.Declare.set ontop [@ocaml.warning "-3"];
      Vernacstate.freeze_interp_state ~marshallable:false
    ) st
  with exn ->
    let exn = Exninfo.capture exn in
    let exn = locate_if_not_already ?loc:cmd.CAst.loc exn in
    Vernacstate.invalidate_cache ();
    Exninfo.iraise exn

(* Regular interp *)
let interp ?(verbosely=true) ~st cmd =
  interp_gen ~verbosely ~st ~interp_fn:interp_control cmd

let interp_qed_delayed_proof ~proof ~info ~st ~control pe : Vernacstate.t =
  interp_gen ~verbosely:false ~st
    ~interp_fn:(interp_qed_delayed_control ~proof ~info ~control) pe
