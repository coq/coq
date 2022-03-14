(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs
open Coqcargs

let fatal_error msg =
  Topfmt.std_logger Feedback.Error msg;
  flush_all ();
  exit 1

(******************************************************************************)
(* Interactive Load File Simulation                                           *)
(******************************************************************************)

let load_init_file opts ~state =
  if opts.pre.load_rcfile then
    Topfmt.(in_phase ~phase:LoadingRcFile) (fun () ->
        Coqrc.load_rcfile ~rcfile:opts.config.rcfile ~state) ()
  else begin
    Flags.if_verbose Feedback.msg_info (str"Skipping rcfile loading.");
    state
  end

let load_vernacular opts ~state =
  List.fold_left
    (fun state (f_in, echo) ->
      let s = Loadpath.locate_file f_in in
      (* Should make the beautify logic clearer *)
      let load_vernac f = Vernac.load_vernac ~echo ~interactive:false ~check:true ~state f in
      if !Flags.beautify
      then Flags.with_option Flags.beautify_file load_vernac f_in
      else load_vernac s
    ) state opts.pre.load_vernacular_list

let load_init_vernaculars opts ~state =
  let state = load_init_file opts ~state in
  let state = load_vernacular opts ~state in
  state

(******************************************************************************)
(* File Compilation                                                           *)
(******************************************************************************)
let warn_file_no_extension =
  CWarnings.create ~name:"file-no-extension" ~category:"filesystem"
         (fun (f,ext) ->
          str "File \"" ++ str f ++
            strbrk "\" has been implicitly expanded to \"" ++
            str f ++ str ext ++ str "\"")

let ensure_ext ext f =
  if Filename.check_suffix f ext then f
  else begin
    warn_file_no_extension (f,ext);
    f ^ ext
  end

let chop_extension f =
  try Filename.chop_extension f with _ -> f

let ensure_bname src tgt =
  let src, tgt = Filename.basename src, Filename.basename tgt in
  let src, tgt = chop_extension src, chop_extension tgt in
  if src <> tgt then
    fatal_error (str "Source and target file names must coincide, directories can differ" ++ fnl () ++
                   str "Source: " ++ str src                                                ++ fnl () ++
                   str "Target: " ++ str tgt)

let ensure ext src tgt = ensure_bname src tgt; ensure_ext ext tgt

let ensure_exists f =
  if not (Sys.file_exists f) then
    fatal_error (hov 0 (str "Can't find file" ++ spc () ++ str f))

let ensure_exists_with_prefix f_in f_out src_suffix tgt_suffix =
  let long_f_dot_src = ensure src_suffix f_in f_in in
  ensure_exists long_f_dot_src;
  let long_f_dot_tgt = match f_out with
    | None -> chop_extension long_f_dot_src ^ tgt_suffix
    | Some f -> ensure tgt_suffix long_f_dot_src f in
  long_f_dot_src, long_f_dot_tgt

let create_empty_file filename =
  let f = open_out filename in
  close_out f

let check_pending_proofs filename =
  let pfs = Vernacstate.Declare.get_all_proof_names () [@ocaml.warning "-3"] in
  if not (CList.is_empty pfs) then
    fatal_error (str "There are pending proofs in file " ++ str filename ++ str": "
                 ++ (pfs
                     |> List.rev
                     |> prlist_with_sep pr_comma Names.Id.print)
                 ++ str ".");
  let pm = Vernacstate.Declare.get_program () [@ocaml.warning "-3"] in
  let what_for = Pp.str ("file " ^ filename) in
  NeList.iter (fun pm -> Declare.Obls.check_solved_obligations ~what_for ~pm) pm

(* Compile a vernac file *)
let compile opts stm_options injections copts ~echo ~f_in ~f_out =
  let open Vernac.State in
  let output_native_objects = match opts.config.native_compiler with
    | NativeOff -> false | NativeOn {ondemand} -> not ondemand
  in
  let mode = copts.compilation_mode in
  let ext_in, ext_out =
     match mode with
     | BuildVo -> ".v", ".vo"
     | BuildVio -> ".v", ".vio"
     | Vio2Vo -> ".vio", ".vo"
     | BuildVos -> ".v", ".vos"
     | BuildVok -> ".v", ".vok"
  in
  let long_f_dot_in, long_f_dot_out =
    ensure_exists_with_prefix f_in f_out ext_in ext_out in
  let dump_empty_vos () =
    let long_f_dot_vos = (chop_extension long_f_dot_out) ^ ".vos" in
    create_empty_file long_f_dot_vos in
  let dump_empty_vok () =
    let long_f_dot_vok = (chop_extension long_f_dot_out) ^ ".vok" in
    create_empty_file long_f_dot_vok in
  match mode with
  | BuildVo | BuildVok ->
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VoDoc long_f_dot_out; injections; stm_options; } in
      let state = { doc; sid; proof = None; time = opts.config.time } in
      let state = load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_out)
        ~v_file:long_f_dot_in);

      Dumpglob.push_output copts.glob_out;
      Dumpglob.start_dump_glob ~vfile:long_f_dot_in ~vofile:long_f_dot_out;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");

      let wall_clock1 = Unix.gettimeofday () in
      let check = Stm.AsyncOpts.(stm_options.async_proofs_mode = APoff) in
      let state = Vernac.load_vernac ~echo ~check ~interactive:false ~state ~ldir long_f_dot_in in
      let _doc = Stm.join ~doc:state.doc in
      let wall_clock2 = Unix.gettimeofday () in
      check_pending_proofs long_f_dot_in;
      (* In .vo production, dump a complete .vo file. *)
      if mode = BuildVo
        then Library.save_library_to ~output_native_objects Library.ProofsTodoNone ldir long_f_dot_out;
      Aux_file.record_in_aux_at "vo_compile_time"
        (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
      Aux_file.stop_aux_file ();
      (* Additionally, dump an empty .vos file to make sure that
        stale ones are never loaded *)
      if mode = BuildVo then
        dump_empty_vos();
      (* In both .vo, and .vok production mode, dump an empty .vok file to
         indicate that proofs are ok. *)
      dump_empty_vok();
      Dumpglob.end_dump_glob ()

  | BuildVio | BuildVos ->
      (* We need to disable error resiliency, otherwise some errors
         will be ignored in batch mode. c.f. #6707

         This is not necessary in the vo case as it fully checks the
         document anyways. *)
      let stm_options = let open Stm.AsyncOpts in
        { stm_options with
          async_proofs_mode = APon;
          async_proofs_n_workers = 0;
          async_proofs_cmd_error_resilience = false;
          async_proofs_tac_error_resilience = FNone;
        } in

      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VioDoc long_f_dot_out; injections; stm_options;
              } in

      let state = { doc; sid; proof = None; time = opts.config.time } in
      let state = load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      let state = Vernac.load_vernac ~echo ~check:false ~interactive:false ~state long_f_dot_in in
      let doc = Stm.finish ~doc:state.doc in
      check_pending_proofs long_f_dot_in;
      let create_vos = (mode = BuildVos) in
      (* In .vos production, the output .vos file contains compiled statements.
         In .vio production, the output .vio file contains compiled statements and suspended proofs. *)
      let () = ignore (Stm.snapshot_vio ~create_vos ~doc ~output_native_objects ldir long_f_dot_out) in
      Stm.reset_task_queue ();
      (* In .vio production, dump an empty .vos file to indicate that the .vio should be loaded. *)
      if mode = BuildVio then dump_empty_vos()

  | Vio2Vo ->
      Flags.async_proofs_worker_id := "Vio2Vo";
      let sum, lib, univs, tasks, proofs =
        Library.load_library_todo long_f_dot_in in
      let univs, proofs = Stm.finish_tasks long_f_dot_out univs proofs tasks in
      Library.save_library_raw long_f_dot_out sum lib univs proofs;
      (* Like in direct .vo production, dump an empty .vok file and an empty .vos file. *)
      dump_empty_vos();
      create_empty_file (long_f_dot_out ^ "k")

let compile opts stm_opts copts injections ~echo ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile opts stm_opts injections copts ~echo ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file opts stm_opts copts injections (f_in, echo) =
  let f_out = copts.compilation_output_name in
  if !Flags.beautify then
    Flags.with_option Flags.beautify_file
      (fun f_in -> compile opts stm_opts copts injections ~echo ~f_in ~f_out) f_in
  else
    compile opts stm_opts copts injections ~echo ~f_in ~f_out

let compile_file opts stm_opts copts injections =
  Option.iter (compile_file opts stm_opts copts injections) copts.compile_file

(******************************************************************************)
(* VIO Dispatching                                                            *)
(******************************************************************************)
let check_vio_tasks copts =
  Flags.async_proofs_worker_id := "VioChecking";
  let rc =
    List.fold_left (fun acc (n,f) ->
        let f_in = ensure ".vio" f f in
        ensure_exists f_in;
        Vio_checking.check_vio (n,f_in) && acc)
      true copts.vio_tasks in
  if not rc then fatal_error Pp.(str "VIO Task Check failed")

(* vio files *)
let schedule_vio copts =
  let l =
    List.map (fun f -> let f_in = ensure ".vio" f f in ensure_exists f_in; f_in)
      copts.vio_files in
  if copts.vio_checking then
    Vio_checking.schedule_vio_checking copts.vio_files_j l
  else
    Vio_checking.schedule_vio_compilation copts.vio_files_j l

let do_vio opts copts _injections =
  (* Vio compile pass *)
  if copts.vio_files <> [] then schedule_vio copts;
  (* Vio task pass *)
  if copts.vio_tasks <> [] then check_vio_tasks copts
