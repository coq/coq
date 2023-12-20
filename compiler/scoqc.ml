(* Simple Coq compiler *)

let _print_st_stats
    { Vernacstate.synterp = { parsing; _ }
    ; interp = { system; lemmas; _ }
    } =
  (* Compact the heap, just in case. *)
  Gc.compact ();
  Format.eprintf "State stats:@\n%!";
  Format.eprintf " [parsing] mem reach: %d@\n%!" (Obj.reachable_words (Obj.magic parsing));
  Format.eprintf " [system ] mem reach: %d@\n%!" (Obj.reachable_words (Obj.magic system));
  Format.eprintf " [lemmas ] mem reach: %d@\n%!" (Obj.reachable_words (Obj.magic lemmas));
  (* Diabled for now *)
  (* Vernacstate.System.print_stats system; *)
  ()

let parse ~st pa =
  let mode = Option.map (fun _ -> Synterp.get_default_proof_mode ()) st.Vernacstate.interp.lemmas in
  Vernacstate.(Parser.parse st.synterp.parsing Pvernac.(main_entry mode)) pa

let error_loc = ref None

let loc_of_cmd (cmd : Vernacexpr.vernac_control) = cmd.loc

let execute ~st cmd : Vernacstate.t =
  try Vernacinterp.interp ~st cmd
  with exn ->
    let exn, info = Exninfo.capture exn in
    error_loc := loc_of_cmd cmd;
    Exninfo.iraise (exn,info)

(* XXX: Fix merge for time not being doing in vernacinterp *)
let time_output ~time stm tstart tend =
  match time with
  | None -> ()
  | Some Coqargs.ToFeedback ->
    let pp = Pp.(Topfmt.pr_cmd_header stm ++ System.fmt_time_difference tstart tend) in
    Feedback.msg_notice pp
  | Some (ToFile _file) -> ()

let init_st = ref None

let execute ~st (cmd : Vernacexpr.vernac_control) =
  match cmd.v.expr with
  | Vernacexpr.VernacSynPure VernacResetInitial -> Option.get !init_st
  | _ -> execute ~st cmd

let rec cloop ~time ~st pa =
  match parse ~st pa with
  | None ->
    st
  | Some stm ->
    let t_start = System.get_time () in
    let st = execute ~st stm in
    let t_end = System.get_time () in
    let () = time_output ~time stm t_start t_end in
    (cloop [@ocaml.tailcall]) ~time ~st pa

let touch_file f =
  let out = open_out f in
  output_char out ' ';
  close_out out

let output_native_objects =
  match Coq_config.native_compiler with
  | NativeOn _ -> true
  | NativeOff -> false

let save_library ldir in_file ~out_file =
  let out_vo = Option.default (Filename.(remove_extension in_file) ^ ".vo") out_file in
  let todo_proofs = Library.ProofsTodoNone in
  Library.save_library_to todo_proofs ~output_native_objects ldir out_vo;

  let out_aux, out_timings =
    let d, f = Filename.dirname in_file, Filename.basename in_file in
    let f = Filename.(remove_extension f) in
    d ^ Filename.dir_sep ^ "." ^ f ^ ".aux",
    d ^ Filename.dir_sep ^ f ^ ".timing"
  in
  touch_file out_aux;
  touch_file out_timings

let start_glob ~in_file =
  let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
  Dumpglob.push_output Dumpglob.MultFiles;
  Dumpglob.start_dump_glob ~vfile:in_file ~vofile:out_vo;
  (* Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n"); *)
  ()

let touch_vos ~in_file =
  let out_vos = Filename.(remove_extension in_file) ^ ".vos" in
  Stdlib.open_out out_vos |> Stdlib.close_out

let rec process_extra args = match args with
  | "-fake-source" :: _ :: rem
  | "-async-proofs-tac-j" :: _ :: rem ->
    process_extra rem
  | "-o" :: file :: rem ->
    let _, extra = process_extra rem in
    Some file, extra
  | r :: rem ->
    let file, extra = process_extra rem in
    file, r :: extra
  | [] -> None, []

let compile_file ~args ~injections ~root_st ~out_file in_file =
  let () = Vernacstate.unfreeze_full_state root_st in
  let f_in = open_in in_file in
  let () = start_glob ~in_file in
  let libname = Util.dirpath_of_file in_file in
  let () = Coqinit.start_library ~top:libname injections in
  let st = Vernacstate.freeze_full_state () in
  let loc = Loc.(initial (InFile { dirpath = None; file = in_file })) in
  let pa = Pcoq.Parsable.make ~loc (Gramlib.Stream.of_channel f_in) in
  let time = args.Coqargs.time in
  let _st = cloop ~time ~st pa in
  (* print_st_stats st; *)
  let () = save_library libname in_file ~out_file in
  let () = touch_vos ~in_file in
  Dumpglob.end_dump_glob ();
  ()

let compile_files ~args ~injections ~extra =
  let root_st = Vernacstate.freeze_full_state () in
  match process_extra extra with
  | None, in_files ->
    List.iter (compile_file ~args ~injections ~root_st ~out_file:None) in_files
  | Some _ as out_file, [in_file] ->
    compile_file ~args ~injections ~root_st ~out_file in_file
  | Some _, _ ->
    CErrors.user_err (Pp.str "Can't use -o on multiple or empty file list")

let () =
  Flags.quiet := true;
  System.trust_file_cache := true;
  Coqinit.init_ocaml ();
  let usage = { Boot.Usage.executable_name = "coqc"
              ; extra_args = ""
              ; extra_options = ""
              } in
  try
    let parse_extra l = (l, []) in
    let args, extra = Coqinit.parse_arguments ~parse_extra ~usage () in
    ignore (Feedback.add_feeder Util.fb_handler);
    let injections = Coqinit.init_runtime args in
    compile_files ~args:(args.config) ~injections ~extra
  with exn ->
    let exn, info = Exninfo.capture exn in
    let loc = Option.append (Loc.get_loc info) !error_loc in
    let pr_loc loc = Pp.(Loc.pr loc ++ str ":" ++ fnl()) in
    Format.eprintf "%aError: @[%a@]@\n%!" Pp.pp_with (Pp.pr_opt pr_loc loc) Pp.pp_with (CErrors.print exn);
    exit 1
