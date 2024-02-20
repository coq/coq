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
open CErrors
open CAst
open Util
open Names
open Libnames
open Vernacexpr
open Locality
open Attributes

(* Default proof mode, to be set at the beginning of proofs for
   programs that cannot be statically classified. *)
let proof_mode_opt_name = ["Default";"Proof";"Mode"]

let { Goptions.get = get_default_proof_mode } =
  Goptions.declare_interpreted_string_option_and_ref
    ~stage:Summary.Stage.Synterp
    ~key:proof_mode_opt_name
    ~value:(Pvernac.register_proof_mode "Noedit" Pvernac.Vernac_.noedit_mode)
    (fun name -> match Pvernac.lookup_proof_mode name with
    | Some pm -> pm
    | None -> CErrors.user_err Pp.(str (Format.sprintf "No proof mode named \"%s\"." name)))
    Pvernac.proof_mode_to_string
    ()

let module_locality = Attributes.Notations.(locality >>= fun l -> return (make_module_locality l))

let with_locality ~atts f =
  let local = Attributes.(parse locality atts) in
  f ~local

let with_module_locality ~atts f =
  let module_local = Attributes.(parse module_locality atts) in
  f ~module_local

let warn_legacy_export_set =
  CWarnings.create ~name:"legacy-export-set" ~category:Deprecation.Version.v8_18
    Pp.(fun () -> strbrk "Syntax \"Export Set\" is deprecated, use the attribute syntax \"#[export] Set\" instead.")

let deprecated_nonuniform =
  CWarnings.create ~name:"deprecated-nonuniform-attribute"
    ~category:Deprecation.Version.v8_18
    Pp.(fun () -> strbrk "Attribute '#[nonuniform]' is deprecated, \
                          use '#[warning=\"-uniform-inheritance\"]' instead.")

let warnings_att =
  Attributes.attribute_of_list [
    "warnings", Attributes.payload_parser ~cat:(^) ~name:"warnings";
    "warning", Attributes.payload_parser ~cat:(^) ~name:"warning";
  ]

let with_generic_atts ~check atts f =
  let atts, warnings = Attributes.parse_with_extra warnings_att atts in
  let atts, nonuniform = Attributes.parse_with_extra ComCoercion.nonuniform atts in
  let warnings =
    let () = if nonuniform <> None && check then deprecated_nonuniform () in
    if nonuniform <> Some true then warnings else
      let ui = "-uniform-inheritance" in
      Some (match warnings with Some w -> w ^ "," ^ ui | None -> ui) in
  match warnings with
  | None -> f ~atts
  | Some warnings ->
    if check then CWarnings.check_unknown_warnings warnings;
    CWarnings.with_warn warnings (fun () -> f ~atts) ()

type module_entry = Modintern.module_struct_expr * Names.ModPath.t * Modintern.module_kind * Entries.inline

type control_entry =
  | ControlTime of { synterp_duration: System.duration }
  | ControlInstructions of { synterp_instructions: System.instruction_count }
  | ControlRedirect of string
  | ControlTimeout of { remaining : float }
  | ControlFail of { st : Vernacstate.Synterp.t }
  | ControlSucceed of { st : Vernacstate.Synterp.t }

type synterp_entry =
  | EVernacNoop
  | EVernacNotation of { local : bool; decl : Metasyntax.notation_interpretation_decl }
  | EVernacBeginSection of lident
  | EVernacEndSegment of lident
  | EVernacRequire of
      Library.library_t list * DirPath.t list * export_with_cats option * (qualid * import_filter_expr) list
  | EVernacImport of (export_flag *
      Libobject.open_filter) *
      (Names.ModPath.t CAst.t * import_filter_expr) list
  | EVernacDeclareModule of Lib.export * lident *
      Declaremods.module_params_expr *
      module_entry
  | EVernacDefineModule of Lib.export * lident *
      Declaremods.module_params_expr *
      ((export_flag * Libobject.open_filter) * Names.ModPath.t) list *
      module_entry Declaremods.module_signature *
      module_entry list
  | EVernacDeclareModuleType of lident *
      Declaremods.module_params_expr *
      ((export_flag * Libobject.open_filter) * Names.ModPath.t) list *
      module_entry list *
      module_entry list
  | EVernacInclude of Declaremods.module_expr list
  | EVernacSetOption of { export : bool; key : Goptions.option_name; value : Vernacexpr.option_setting }
  | EVernacLoad of Vernacexpr.verbose_flag * (vernac_control_entry * Vernacstate.Synterp.t) list
  | EVernacExtend of Vernactypes.typed_vernac

and vernac_entry = synterp_entry Vernacexpr.vernac_expr_gen

and vernac_control_entry = (control_entry, synterp_entry) Vernacexpr.vernac_control_gen_r CAst.t

let synterp_reserved_notation ~module_local ~infix l =
  Metasyntax.add_reserved_notation ~local:module_local ~infix l

let synterp_custom_entry ~module_local s =
  Metasyntax.declare_custom_entry module_local s

(* Assumes cats is irrelevant if f is ImportNames *)
let import_module_syntax_with_filter ~export cats m f =
  match f with
  | ImportAll -> Declaremods.Synterp.import_module cats ~export m
  | ImportNames ns -> ()

let synterp_import_mod (export,cats) qid f =
  let loc = qid.loc in
  let m = try Nametab.locate_module qid
    with Not_found ->
      CErrors.user_err ?loc Pp.(str "Cannot find module " ++ pr_qualid qid)
  in
  import_module_syntax_with_filter ~export cats m f; m

let synterp_import_cats cats =
  Option.cata
    (fun cats -> Libobject.make_filter ~finite:(not cats.negative) cats.import_cats)
    Libobject.unfiltered
    cats

let check_no_filter_when_using_cats l =
  List.iter (function
      | _, ImportAll -> ()
      | q, ImportNames _ ->
        CErrors.user_err ?loc:q.loc
          Pp.(str "Cannot combine importing by categories and importing by names."))
    l

let synterp_import export refl =
  if Option.has_some (snd export) then check_no_filter_when_using_cats refl;
  let export = on_snd synterp_import_cats export in
  export, List.map (fun (qid,f) -> CAst.make ?loc:qid.loc @@ synterp_import_mod export qid f, f) refl

let synterp_define_module export {loc;v=id} (binders_ast : module_binder list) mty_ast_o mexpr_ast_l =
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  let export = Option.map (on_snd synterp_import_cats) export in
  match mexpr_ast_l with
    | [] ->
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> Option.map (on_snd synterp_import_cats) export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp, args, sign = Declaremods.Synterp.start_module export id binders_ast mty_ast_o in
       let argsexports = List.map_filter
         (fun (export,id) ->
          Option.map (fun export ->
            export, synterp_import_mod export (qualid_of_ident id) ImportAll
          ) export
         ) argsexport
       in
       export, args, argsexports, [], sign
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if not (Option.is_empty export) then
           user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
       let mp, args, expr, sign =
         Declaremods.Synterp.declare_module
           id binders_ast mty_ast_o mexpr_ast_l
       in
       Option.iter (fun (export,cats) ->
        ignore (synterp_import_mod (export,cats) (qualid_of_ident id) ImportAll)) export;
       export, args, [], expr, sign

let synterp_declare_module_type_syntax {loc;v=id} binders_ast mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  match mty_ast_l with
    | [] ->
       let binders_ast,argsexport =
         List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> Option.map (on_snd synterp_import_cats) export,i)idl)@argsexport) binders_ast
             ([],[]) in

       let mp, args, sign = Declaremods.Synterp.start_modtype id binders_ast mty_sign in
       let argsexport =
         List.map_filter
           (fun (export,id) ->
             Option.map
               (fun export -> export, synterp_import_mod export (qualid_of_ident ?loc id) ImportAll) export
           ) argsexport
       in
       args, argsexport, [], sign
    | _ :: _ ->
        let binders_ast = List.map
          (fun (export,idl,ty) ->
            if not (Option.is_empty export) then
              user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
            else (idl,ty)) binders_ast in
        let mp, args, expr, sign = Declaremods.Synterp.declare_modtype id binders_ast mty_sign mty_ast_l in
        args, [], expr, sign

let synterp_declare_module export {loc;v=id} binders_ast mty_ast =
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if not (Option.is_empty export) then
      user_err Pp.(str "Arguments of a functor declaration cannot be exported. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
     else (idl,ty)) binders_ast in
  let mp, args, expr, sign =
    Declaremods.Synterp.declare_module id binders_ast (Declaremods.Enforce mty_ast) []
  in
  assert (List.is_empty expr);
  let sign = match sign with Declaremods.Enforce x -> x | _ -> assert false in
  let export = Option.map (on_snd synterp_import_cats) export in
  Option.iter (fun export -> ignore @@ synterp_import_mod export (qualid_of_ident id) ImportAll) export;
  mp, export, args, sign

let synterp_include l = Declaremods.Synterp.declare_include l

let synterp_end_module export {loc;v=id} =
  let _ = Declaremods.Synterp.end_module () in
  Option.map (fun export -> synterp_import_mod export (qualid_of_ident ?loc id) ImportAll) export

let synterp_end_section {CAst.loc; v} =
  Dumpglob.dump_reference ?loc
    (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
  Lib.Synterp.close_section ()

let synterp_end_segment ({v=id} as lid) =
  let ss = Lib.Synterp.find_opening_node id in
  match ss with
  | Lib.OpenedModule (false,export,_,_) -> ignore (synterp_end_module export lid)
  | Lib.OpenedModule (true,_,_,_) -> ignore (Declaremods.Synterp.end_modtype ())
  | Lib.OpenedSection _ -> synterp_end_section lid
  | _ -> assert false

let err_unmapped_library ?from qid =
  let prefix = match from with
  | None -> mt ()
  | Some from ->
    str " with prefix " ++ DirPath.print from
  in
  strbrk "Cannot find a physical path bound to logical path "
    ++ pr_qualid qid ++ prefix ++ str "."

let err_notfound_library ?from qid =
  let prefix = match from with
  | None -> mt ()
  | Some from -> str " with prefix " ++ DirPath.print from
  in
  let bonus =
    if !Flags.load_vos_libraries then mt ()
    else str " (while searching for a .vos file)"
  in
  strbrk "Unable to locate library " ++ pr_qualid qid ++ prefix ++ bonus
    ++ str "."

exception UnmappedLibrary of Names.DirPath.t option * Libnames.qualid
exception NotFoundLibrary of Names.DirPath.t option * Libnames.qualid


let _ = CErrors.register_handler begin function
  | UnmappedLibrary (from, qid) -> Some (err_unmapped_library ?from qid)
  | NotFoundLibrary (from, qid) -> Some (err_notfound_library ?from qid)
  | _ -> None
end

let synterp_require from export qidl =
  let root = match from with
  | None -> None
  | Some from ->
    let (hd, tl) = Libnames.repr_qualid from in
    Some (Libnames.add_dirpath_suffix hd tl)
  in
  let locate (qid,_) =
    let open Loadpath in
    match locate_qualified_library ?root qid with
    | Ok (dir,_) -> (qid.loc, dir)
    | Error LibUnmappedDir -> Loc.raise ?loc:qid.loc (UnmappedLibrary (root, qid))
    | Error LibNotFound -> Loc.raise ?loc:qid.loc (NotFoundLibrary (root, qid))
  in
  let modrefl = List.map locate qidl in
  let lib_resolver = Loadpath.try_locate_absolute_library in
  let filenames = Library.require_library_syntax_from_dirpath ~lib_resolver modrefl in
  Option.iter (fun (export,cats) ->
      let cats = synterp_import_cats cats in
      List.iter2 (fun (_, m) (_, f) ->
          import_module_syntax_with_filter ~export cats (MPfile m) f)
        modrefl qidl)
    export;
    filenames, List.map snd modrefl

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) filename

let synterp_declare_ml_module ~local l =
  let local = Option.default false local in
  let l = List.map expand l in
  Mltop.declare_ml_modules local l

let synterp_chdir = function
  | None -> Feedback.msg_notice (str (Sys.getcwd()))
  | Some path ->
      begin
        try Sys.chdir (expand path)
        with Sys_error err ->
          (* Cd is typically used to control the output directory of
          extraction. A failed Cd could lead to overwriting .ml files
          so we make it an error. *)
          user_err Pp.(str ("Cd failed: " ^ err))
      end;
      Flags.if_verbose Feedback.msg_info (str (Sys.getcwd()))

(* External dependencies *)

let synterp_extra_dep ?loc from file id =
  if Lib.sections_are_opened () then
    user_err ?loc Pp.(str "Extra Dependencies cannot be declared inside sections.");
  let hd, tl = Libnames.repr_qualid from in
  let from = Libnames.add_dirpath_suffix hd tl in
  ComExtraDeps.declare_extra_dep ?loc ~from ~file id

let synterp_begin_section ({v=id} as lid) =
  Dumpglob.dump_definition lid true "sec";
  Lib.Synterp.open_section id

(** A global default timeout, controlled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let check_timeout n =
  if n <= 0 then CErrors.user_err Pp.(str "Timeout must be > 0.")

(* Timeout *)
let with_timeout ~timeout:n (f : 'a -> 'b) (x : 'a) : 'b =
  check_timeout n;
  let n = float_of_int n in
  let start = Unix.gettimeofday () in
  begin match Control.timeout n f x with
  | None -> Exninfo.iraise (Exninfo.capture CErrors.Timeout)
  | Some (ctrl,v) ->
    let stop = Unix.gettimeofday () in
    let remaining = n -. (start -. stop) in
    if remaining <= 0. then Exninfo.iraise (Exninfo.capture CErrors.Timeout)
    else ControlTimeout { remaining } :: ctrl, v
  end

let test_mode = ref false

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Loc.t option * Pp.t, 'a) result =
  try
    let x = f () in
    Error x
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

let with_fail ~loc f =
  let st = Vernacstate.Synterp.freeze () in
  let res = with_fail f in
  let transient_st = Vernacstate.Synterp.freeze () in
  Vernacstate.Synterp.unfreeze st;
  match res with
  | Error (ctrl, v) ->
    ControlFail { st = transient_st } :: ctrl, v
  | Ok (eloc, msg) ->
    let loc = if !test_mode then real_error_loc ~cmdloc:loc ~eloc else None in
    if not !Flags.quiet || !test_mode
    then Feedback.msg_notice ?loc Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg);
    [], VernacSynterp EVernacNoop

let with_succeed f =
  let st = Vernacstate.Synterp.freeze () in
  let (ctrl, v) = f () in
  let transient_st = Vernacstate.Synterp.freeze () in
  Vernacstate.Synterp.unfreeze st;
  ControlSucceed { st = transient_st } :: ctrl, v

(* We restore the state always *)
let rec synterp_control_flag ~loc (f : control_flag list)
    (fn : vernac_expr -> vernac_entry) expr =
  match f with
  | [] -> [], fn expr
  | ControlFail :: l ->
    with_fail ~loc (fun () -> synterp_control_flag ~loc l fn expr)
  | ControlSucceed :: l ->
    with_succeed (fun () -> synterp_control_flag ~loc l fn expr)
  | ControlTimeout timeout :: l ->
    with_timeout ~timeout (synterp_control_flag ~loc l fn) expr
  | ControlTime :: l ->
    begin match System.measure_duration (synterp_control_flag ~loc l fn) expr with
    | Ok((ctrl,v), synterp_duration) ->
      ControlTime { synterp_duration } :: ctrl, v
    | Error(exn, synterp_duration) as e ->
      Feedback.msg_notice @@ System.fmt_transaction_result e;
      Exninfo.iraise exn
    end
  | ControlInstructions :: l ->
    begin match System.count_instructions (synterp_control_flag ~loc l fn) expr with
    | Ok((ctrl,v), synterp_instructions) ->
      ControlInstructions { synterp_instructions } :: ctrl, v
    | Error(exn, synterp_instructions) as e ->
      Feedback.msg_notice @@ System.fmt_instructions_result e;
      Exninfo.iraise exn
    end
  | ControlRedirect s :: l ->
    let (ctrl, v) = Topfmt.with_output_to_file s (synterp_control_flag ~loc l fn) expr in
    (ControlRedirect s :: ctrl, v)

let rec synterp ?loc ~atts v =
  match v with
  | VernacSynterp v0 ->
    let e = begin match v0 with
    | VernacReservedNotation (infix, sl) ->
      with_module_locality ~atts synterp_reserved_notation ~infix sl;
      EVernacNoop
    | VernacNotation (infix,ntn_decl) ->
      let local, user_warns = Attributes.(parse Notations.(module_locality ++ user_warns) atts) in
      let decl = Metasyntax.add_notation_syntax ~local ~infix user_warns ntn_decl in
      EVernacNotation { local; decl }
    | VernacDeclareCustomEntry s ->
      with_module_locality ~atts synterp_custom_entry s;
      EVernacNoop
    | VernacDefineModule (export,lid,bl,mtys,mexprl) ->
      let export, args, argsexport, expr, sign = synterp_define_module export lid bl mtys mexprl in
      EVernacDefineModule (export,lid,args,argsexport,sign,expr)
    | VernacDeclareModuleType (lid,bl,mtys,mtyo) ->
      let args, argsexport, expr, sign = synterp_declare_module_type_syntax lid bl mtys mtyo in
      EVernacDeclareModuleType (lid,args,argsexport,sign,expr)
    | VernacDeclareModule (export,lid,bl,mtyo) ->
      let mp, export, args, sign =
        synterp_declare_module export lid bl mtyo
      in
      EVernacDeclareModule (export,lid,args,sign)
    | VernacInclude in_asts ->
      EVernacInclude (synterp_include in_asts)
    | VernacBeginSection lid ->
      synterp_begin_section lid;
      EVernacBeginSection lid
    | VernacEndSegment lid ->
      synterp_end_segment lid;
      EVernacEndSegment lid
    | VernacRequire (from, export, qidl) ->
      let needed, modrefl = synterp_require from export qidl in
      EVernacRequire (needed, modrefl, export, qidl)
    | VernacImport (export,qidl) ->
      let export, mpl = synterp_import export qidl in
      EVernacImport (export,mpl)
    | VernacDeclareMLModule l ->
      with_locality ~atts synterp_declare_ml_module l;
      EVernacNoop
    | VernacChdir s ->
      unsupported_attributes atts;
      synterp_chdir s;
      EVernacNoop
    | VernacExtraDependency(from,file,id) ->
      unsupported_attributes atts;
      synterp_extra_dep ?loc from file id;
      EVernacNoop

    | VernacSetOption (export,key,value) ->
      let atts = if export then begin
          warn_legacy_export_set ?loc ();
          CAst.make ?loc ("export", VernacFlagEmpty) :: atts
        end
        else atts
      in
      let locality = parse option_locality atts in
      Vernacoptions.vernac_set_option ~locality ~stage:Summary.Stage.Synterp key value;
      EVernacSetOption { export; key; value }
    | VernacProofMode mn ->
      unsupported_attributes atts;
      EVernacNoop
    | VernacLoad (verbosely, fname) ->
      unsupported_attributes atts;
      synterp_load verbosely fname
    | VernacExtend (opn,args) ->
      let f = Vernacextend.type_vernac ?loc ~atts opn args () in
      EVernacExtend(f)
    end in
    VernacSynterp e
  | VernacSynPure x -> VernacSynPure x

and synterp_load verbosely fname =
  let fname =
    Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (Pp.str x)) fname in
  let fname = CUnix.make_suffix fname ".v" in
  let input =
    let longfname = Loadpath.locate_file fname in
    let in_chan = Util.open_utf8_file_in longfname in
    Pcoq.Parsable.make ~loc:Loc.(initial (InFile { dirpath=None; file=longfname}))
        (Gramlib.Stream.of_channel in_chan) in
  (* Parsing loop *)
  let v_mod = if verbosely then Flags.verbosely else Flags.silently in
  let parse_sentence proof_mode =
    Pcoq.Entry.parse (Pvernac.main_entry proof_mode)
  in
  let proof_mode = Some (get_default_proof_mode ()) in
  let rec load_loop entries =
    match parse_sentence proof_mode input with
    | None -> entries
    | Some cmd ->
      let entry = v_mod synterp_control cmd in
      let st = Vernacstate.Synterp.freeze () in
      (load_loop [@ocaml.tailcall]) ((entry,st)::entries)
  in
  let entries = List.rev @@ load_loop [] in
  EVernacLoad(verbosely, entries)

and synterp_control CAst.{ loc; v = cmd } =
  let fn expr =
    with_generic_atts ~check:true cmd.attrs (fun ~atts ->
        synterp ?loc ~atts cmd.expr)
  in
  let control, expr = synterp_control_flag ~loc cmd.control fn cmd.expr in
  CAst.make ?loc { expr; control; attrs = cmd.attrs }

let default_timeout = ref None

let () = let open Goptions in
  declare_int_option
    { optstage = Summary.Stage.Synterp;
      optdepr  = None;
      optkey   = ["Default";"Timeout"];
      optread  = (fun () -> !default_timeout);
      optwrite = (fun n -> Option.iter check_timeout n; default_timeout := n) }

let has_timeout ctrl = ctrl |> List.exists (function
    | Vernacexpr.ControlTimeout _ -> true
    | _ -> false)

let synterp_control CAst.{ loc; v = cmd } =
  let control = cmd.control in
  let control = match !default_timeout with
    | None -> control
    | Some n ->
      if has_timeout control then control
      else Vernacexpr.ControlTimeout n :: control
  in
  synterp_control @@ CAst.make ?loc { cmd with control }

let synterp_control cmd =
  Flags.with_option Flags.in_synterp_phase synterp_control cmd
