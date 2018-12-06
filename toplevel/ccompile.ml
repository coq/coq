(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs

let fatal_error msg =
  Topfmt.std_logger Feedback.Error msg;
  flush_all ();
  exit 1

(******************************************************************************)
(* Interactive Load File Simulation                                           *)
(******************************************************************************)
let load_vernacular opts ~state =
  List.fold_left
    (fun state (f_in, echo) ->
      let s = Loadpath.locate_file f_in in
      (* Should make the beautify logic clearer *)
      let load_vernac f = Vernac.load_vernac ~echo ~interactive:false ~check:true ~state f in
      if !Flags.beautify
      then Flags.with_option Flags.beautify_file load_vernac f_in
      else load_vernac s
    ) state (List.rev opts.load_vernacular_list)

let load_init_vernaculars opts ~state =
  let state =
    if opts.load_rcfile then
      Topfmt.(in_phase ~phase:LoadingRcFile) (fun () ->
          Coqinit.load_rcfile ~rcfile:opts.rcfile ~state) ()
    else begin
      Flags.if_verbose Feedback.msg_info (str"Skipping rcfile loading.");
      state
    end in

  load_vernacular opts ~state

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

let ensure_v v = ensure ".v" v v
let ensure_vo v vo = ensure ".vo" v vo

let ensure_exists f =
  if not (Sys.file_exists f) then
    fatal_error (hov 0 (str "Can't find file" ++ spc () ++ str f))

(* Compile a vernac file *)
let compile opts ~echo ~f_in ~f_out =
  let open Vernac.State in
  let check_pending_proofs () =
    let pfs = Proof_global.get_all_proof_names () in
    if not (CList.is_empty pfs) then
      fatal_error (str "There are pending proofs: "
                    ++ (pfs
                        |> List.rev
                        |> prlist_with_sep pr_comma Names.Id.print)
                    ++ str ".")
  in
  let iload_path = build_load_path opts in
  let require_libs = require_libs opts in
  let stm_options = opts.stm_flags in
  match opts.compilation_mode with
  | BuildVo ->
      Flags.record_aux_file := true;
      let long_f_dot_v = ensure_v f_in in
      ensure_exists long_f_dot_v;
      let long_f_dot_vo =
        match f_out with
        | None -> long_f_dot_v ^ "o"
        | Some f -> ensure_vo long_f_dot_v f in

      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc
          Stm.{ doc_type = VoDoc long_f_dot_vo;
                iload_path; require_libs; stm_options;
              } in
      let state = { doc; sid; proof = None; time = opts.time } in
      let state = load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_vo)
        ~v_file:long_f_dot_v);
      Dumpglob.start_dump_glob ~vfile:long_f_dot_v ~vofile:long_f_dot_vo;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");
      let wall_clock1 = Unix.gettimeofday () in
      let check = Stm.AsyncOpts.(stm_options.async_proofs_mode = APoff) in
      let state = Vernac.load_vernac ~echo ~check ~interactive:false ~state long_f_dot_v in
      let _doc = Stm.join ~doc:state.doc in
      let wall_clock2 = Unix.gettimeofday () in
      check_pending_proofs ();
      Library.save_library_to ldir long_f_dot_vo (Global.opaque_tables ());
      Aux_file.record_in_aux_at "vo_compile_time"
        (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
      Aux_file.stop_aux_file ();
      Dumpglob.end_dump_glob ()

let compile opts ~echo ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile opts ~echo ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file opts (f_in, echo) =
  let f_out = opts.compilation_output_name in
  if !Flags.beautify then
    Flags.with_option Flags.beautify_file
      (fun f_in -> compile opts ~echo ~f_in ~f_out) f_in
  else
    compile opts ~echo ~f_in ~f_out

let compile_files opts =
  let compile_list = List.rev opts.compile_list in
  List.iter (compile_file opts) compile_list
