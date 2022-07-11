(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let init color_mode ~opts =
  Flags.quiet := true;
  System.trust_file_cache := true;
  Colors.init_color (if opts.Coqargs.config.Coqargs.print_emacs then `EMACS else color_mode)

module Options = struct

  type 'a t = {
    compilation_output_name : string option;
    compile_file : 'a;
    glob_out : Dumpglob.glob_output;
  }
  let default = {
    compilation_output_name = None;
    compile_file = None;
    glob_out = MultFiles;
  }
  let set x
    ?(compilation_output_name=x.compilation_output_name)
    ?(compile_file=x.compile_file)
    ?(glob_out=x.glob_out)
    ()
  =
    { compilation_output_name; compile_file; glob_out }

  let rec parse o skipped = function
    | [] -> o, List.rev skipped
    | "-o" :: out :: rest ->
      parse (set o ~compilation_output_name:(Some out) ()) skipped rest
    | ("-no-glob" | "-noglob") :: rest ->
      parse (set o ~glob_out:Dumpglob.NoGlob ()) skipped rest
    | "-dump-glob" :: out :: rest ->
      parse (set o ~glob_out:Dumpglob.(File out) ()) skipped rest   
    | "-async-proofs" :: "off" :: rest ->
      parse o skipped rest
    | x :: rest when o.compile_file = None ->
      parse (set o ~compile_file:(Some x) ()) skipped rest
    | x :: rest -> parse o (x :: skipped) rest
        
  let validate {
    compilation_output_name;
    compile_file;
    glob_out
  } =
    let compile_file =
      match compile_file with
      | None -> CErrors.user_err Pp.(str "no file to compile")
      | Some f -> f in
    { compilation_output_name; compile_file; glob_out }

end

let usage = Boot.Usage.{
    executable_name = "coqc";
    extra_args = "file";
    extra_options = {|
coqc specific options:
  -o f.vo                use f.vo as the output file name
  -noglob                do not dump globalizations
  -dump-glob f           dump globalizations in file f (to be used by coqdoc)
|} }


let parse_extra extras =
  let color_mode, extras = Colors.parse_extra_colors extras in
  let c_opts, extras = Options.parse Options.default [] extras in
  (c_opts, color_mode), extras

let warning_feed { Feedback.contents } =
  let open Feedback in
  match contents with
  (* Re-enable when we switch back to feedback-based error printing *)
  | Message (Error,loc,msg) -> ()
  | Message (lvl,loc,msg) ->
    let pre_hdr = Option.map Pp.(fun x -> Loc.pr x ++ str ":") loc in
    Topfmt.std_logger ?pre_hdr lvl msg
  | _ -> ()

let start_glob glob_out top file output_file =
  Dumpglob.push_output glob_out;
  Dumpglob.start_dump_glob ~vfile:file ~vofile:output_file;
  Dumpglob.dump_string ("F" ^ Names.DirPath.to_string top ^ "\n")

let start_aux file output_file =
  Aux_file.(start_aux_file
  ~aux_file:(aux_file_name_for output_file)
  ~v_file:file)

let dump_empty file ext =
  let file = (Common_compile.safe_chop_extension file) ^ ext in
  close_out @@ open_out file

let save_library ~opts state top file output_file =
  Common_compile.ensure_no_pending_proofs ~filename:file state;
  let output_native_objects = match opts.Coqargs.config.native_compiler with
    | Coqargs.NativeOff -> false
    | Coqargs.NativeOn {ondemand} -> not ondemand
  in
  Library.save_library_to ~output_native_objects Library.ProofsTodoNone top output_file

let end_aux time =
  Aux_file.record_in_aux_at "vo_compile_time" (Printf.sprintf "%.3f" time);
  Aux_file.stop_aux_file ()

let setup_in_out { Options.compilation_output_name = tgt ; compile_file = src; glob_out } =
  let file, output_file =
    Common_compile.ensure_exists_with_prefix ~src ~tgt ~src_ext:".v" ~tgt_ext:".vo" in
  let top = Coqargs.(dirpath_of_top (TopPhysical file)) in
  let dirpath = Some (Names.DirPath.to_string top) in
  let loc = Loc.(initial (InFile {dirpath; file = file})) in
  let in_chan = Util.open_utf8_file_in file in
  let in_pa = Pcoq.Parsable.make ~loc (Gramlib.Stream.of_channel in_chan) in
  start_aux file output_file;
  start_glob glob_out top file output_file;
  (top, file, output_file), in_pa, top

let close_in_out ~opts ~time state (top, file, output_file) =
  save_library ~opts state top file output_file;
  end_aux time;
  dump_empty file ".vok";
  dump_empty file ".vos";
  Dumpglob.end_dump_glob ()

module CompatTestSuite = struct
let is_undo ast =
  match ast.CAst.v.Vernacexpr.expr with
  | Vernacexpr.VernacUndo _ -> true
  | _ -> false

let history : Vernacstate.t list ref = ref []
let history_limit = 5

let update_undo_state state =
  if List.length !history = history_limit then
    history := state :: CList.drop_last !history
  else
    history := state :: !history

let handle_undo ast =
  match ast.CAst.v.Vernacexpr.expr with
  | Vernacexpr.VernacUndo i ->
      if i <= history_limit then
        let before, after = CList.chop i !history in
        history := after;
        CList.last before
      else
        CErrors.user_err Pp.(str "Undo limited to " ++ int history_limit)
  | _ -> assert false
      
end

let compile_file ~c_opts ~opts injections =
  let handle, input, top = setup_in_out c_opts in

  let wall_clock1 = Unix.gettimeofday () in
  Coqinit.start_library ~top injections;
  let state = Vernacstate.freeze_interp_state ~marshallable:false in
  (* let state = Load.load_init_vernaculars opts ~state in *)
  let rec loop (state as old_state) =
    let open Vernacstate in
    match Parser.parse state.parsing Pvernac.main_entry input with
    | None -> state
    | Some ast when CompatTestSuite.is_undo ast ->
        let state = CompatTestSuite.handle_undo ast in
        loop state
    | Some ast ->
        let state = Vernacinterp.interp ~verbosely:false ~st:state ast in
        CompatTestSuite.update_undo_state old_state;
        loop state
  in
  let state = loop state in
  let wall_clock2 = Unix.gettimeofday () in
  
  close_in_out ~opts ~time:(wall_clock2 -. wall_clock1) state handle

let main () =
  let _feeder = Feedback.add_feeder warning_feed in
  try
    Coqinit.init_ocaml ();
    let opts, (c_opts, customopts) = Coqinit.parse_arguments ~parse_extra ~usage ~initial_args:Coqargs.default () in
    let c_opts = Options.validate c_opts in
    let injections = Coqinit.init_runtime opts in
    init customopts ~opts;
    compile_file ~c_opts ~opts injections;
    exit 0
  with exn ->
    flush_all();
    Topfmt.print_err_exn exn;
    flush_all();
    let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
    exit exit_code
