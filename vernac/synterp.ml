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

(** Standard attributes for definition-like commands. *)
module DefAttributes = struct
  type t = {
    locality : bool option;
    polymorphic : bool;
    program : bool;
    deprecated : Deprecation.t option;
    canonical_instance : bool;
    typing_flags : Declarations.typing_flags option;
    using : Vernacexpr.section_subset_expr option;
    nonuniform : bool;
    reversible : bool;
  }

  let parse ?(coercion=false) f =
    let open Attributes in
    let nonuniform = if coercion then ComCoercion.nonuniform else Notations.return None in
    let (((((((locality, deprecated), polymorphic), program), canonical_instance), typing_flags), using), nonuniform), reversible =
      parse Notations.(locality ++ deprecation ++ polymorphic ++ program ++ canonical_instance ++ typing_flags ++ using ++ nonuniform ++ reversible) f
    in
    if Option.has_some deprecated then
      Attributes.unsupported_attributes [CAst.make ("deprecated (use a notation and deprecate that instead)",VernacFlagEmpty)];
    let using = Option.map Proof_using.using_from_string using in
    let reversible = Option.default true reversible in
    let nonuniform = Option.default false nonuniform in
    { polymorphic; program; locality; deprecated; canonical_instance; typing_flags; using; nonuniform; reversible }
end

let module_locality = Attributes.Notations.(locality >>= fun l -> return (make_module_locality l))

let with_locality ~atts f =
  let local = Attributes.(parse locality atts) in
  f ~local

let with_section_locality ~atts f =
  let local = Attributes.(parse locality atts) in
  let section_local = make_section_locality local in
  f ~section_local

let with_module_locality ~atts f =
  let module_local = Attributes.(parse module_locality atts) in
  f ~module_local

let with_def_attributes ?coercion ~atts f =
  let atts = DefAttributes.parse ?coercion atts in
  if atts.DefAttributes.program then Declare.Obls.check_program_libraries ();
  f ~atts

type module_entry = Modintern.module_struct_expr * Names.ModPath.t * Modintern.module_kind * Entries.inline
type module_binder_entry = Declaremods.module_params_expr * (Lib.export * Names.Id.t)

(*
type vernac_entry =

  | EVernacNotation of
      Constrexpr.constr_expr * Metasyntax.notation_main_data * Notation.notation_symbols * Constrexpr.notation CAst.t *
      Metasyntax.syntax_rules * Notation.delimiters * Notation_term.scope_name option
  | EVernacDeclareCustomEntry of string

  | EVernacBeginSection of lident
  | EVernacEndSegment of lident
  | EVernacRequire of
      qualid option * export_with_cats option * (qualid * Vernacexpr.import_filter_expr) list
  | EVernacImport of (Vernacexpr.export_flag *
      Libobject.open_filter) *
      (Names.ModPath.t CAst.t * Vernacexpr.import_filter_expr) list

  (* Modules and Module Types *)
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

  (* Auxiliary file and library management *)
  | EVernacAddLoadPath of { implicit : bool
                         ; physical_path : CUnix.physical_path
                         ; logical_path : DirPath.t
                         }

  | EVernacRemoveLoadPath of string
  | EVernacAddMLPath of string
  | EVernacChdir of string option

  (* Resetting *)
  | EVernacResetName of lident
  | EVernacResetInitial
  | EVernacBack of int

  (* Commands *)
  | EVernacCreateHintDb of string * bool
  | EVernacRemoveHints of string list * qualid list
  | EVernacHints of string list * hints_expr
  | EVernacSyntacticDefinition of
      lident * (Id.t list * constr_expr) * syntax_modifier CAst.t list
  | EVernacArguments of
      qualid or_by_notation *
      vernac_argument_status list (* Main arguments status list *) *
      (Name.t * Glob_term.binding_kind) list list (* Extra implicit status lists *) *
      arguments_modifier list
  | EVernacReserve of simple_binder list
  | EVernacGeneralizable of (lident list) option
  | EVernacSetOpacity of (Conv_oracle.level * qualid or_by_notation list)
  | EVernacSetStrategy of
      (Conv_oracle.level * qualid or_by_notation list) list
  | EVernacSetOption of bool (* Export modifier? *) * Goptions.option_name * option_setting
  | EVernacAddOption of Goptions.option_name * Goptions.table_value list
  | EVernacRemoveOption of Goptions.option_name * Goptions.table_value list
  | EVernacMemOption of Goptions.option_name * Goptions.table_value list
  | EVernacPrintOption of Goptions.option_name
  | EVernacCheckMayEval of Genredexpr.raw_red_expr option * Goal_select.t option * constr_expr
  | EVernacGlobalCheck of constr_expr
  | EVernacDeclareReduction of string * Genredexpr.raw_red_expr
  | EVernacPrint of printable
  | EVernacSearch of searchable * Goal_select.t option * search_restriction
  | EVernacLocate of locatable
  | EVernacRegister of qualid * register_kind
  | EVernacPrimitive of ident_decl * CPrimitives.op_or_type * constr_expr option
  | EVernacComments of comment list

  (* Proof management *)
  | EVernacAbort
  | EVernacAbortAll
  | EVernacRestart
  | EVernacUndo of int
  | EVernacUndoTo of int
  | EVernacFocus of int option
  | EVernacUnfocus
  | EVernacUnfocused
  | EVernacBullet of Proof_bullet.t
  | EVernacSubproof of Goal_select.t option
  | EVernacEndSubproof
  | EVernacShow of showable
  | EVernacCheckGuard
  | EVernacProof of Genarg.raw_generic_argument option * section_subset_expr option
  | EVernacNoop

  (* For extension *)
  | EVernacExtend of Vernacextend.typed_vernac

type vernac_entry_control_r =
  { control : control_flag list
  ; attrs : Attributes.vernac_flags
  ; entry : vernac_entry
  }
and vernac_entry_control = vernac_entry_control_r CAst.t
*)

type synterp_entry =
  | EVernacNoop
  | EVernacNotation of
      Constrexpr.constr_expr * Metasyntax.notation_main_data * Notation.notation_symbols * Constrexpr.notation CAst.t *
      Metasyntax.syntax_rules * Notation.delimiters * Notation_term.scope_name option
  | EVernacBeginSection of lident
  | EVernacEndSegment of lident
  | EVernacRequire of
      qualid option * export_with_cats option * (qualid * import_filter_expr) list
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
  | EVernacSetOption of bool (* Export modifier? *) * Goptions.option_name * option_setting
  | EVernacExtend of Vernacextend.typed_vernac

type vernac_entry = synterp_entry Vernacexpr.vernac_expr_gen

type vernac_entry_control = synterp_entry vernac_control_gen_r CAst.t

let vernac_reserved_notation ~module_local ~infix l =
  Metasyntax.add_reserved_notation ~local:module_local ~infix l

let vernac_notation_syntax ~atts ~infix =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Metasyntax.add_notation_syntax ~local:module_local ~infix deprecation

let vernac_custom_entry ~module_local s =
  Metasyntax.declare_custom_entry module_local s

(* Assumes cats is irrelevant if f is ImportNames *)
let import_module_syntax_with_filter ~export cats m f =
  match f with
  | ImportAll -> Declaremods.Synterp.import_module cats ~export m
  | ImportNames ns -> ()

let vernac_import_mod_syntax (export,cats) qid f =
  let loc = qid.loc in
  let m = try Nametab.locate_module qid
    with Not_found ->
      CErrors.user_err ?loc Pp.(str "Cannot find module " ++ pr_qualid qid)
  in
  import_module_syntax_with_filter ~export cats m f; m

let interp_import_cats cats =
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

let vernac_import_syntax export refl =
  CDebug.debug_synterp (fun () -> Pp.(str"vernac_import_syntax"));
  if Option.has_some (snd export) then check_no_filter_when_using_cats refl;
  let export = on_snd interp_import_cats export in
  export, List.map (fun (qid,f) -> CAst.make ?loc:qid.loc @@ vernac_import_mod_syntax export qid f, f) refl

let vernac_define_module_syntax export {loc;v=id} (binders_ast : module_binder list) mty_ast_o mexpr_ast_l =
  let export = Option.map (on_snd interp_import_cats) export in
  match mexpr_ast_l with
    | [] ->
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> Option.map (on_snd interp_import_cats) export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp, args, sign = Declaremods.Synterp.start_module export id binders_ast mty_ast_o in
       let argsexports = List.map_filter
         (fun (export,id) ->
          Option.map (fun export ->
            export, vernac_import_mod_syntax export (qualid_of_ident id) ImportAll
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
        ignore (vernac_import_mod_syntax (export,cats) (qualid_of_ident id) ImportAll)) export;
       export, args, [], expr, sign

let vernac_declare_module_type_syntax {loc;v=id} binders_ast mty_sign mty_ast_l =
  match mty_ast_l with
    | [] ->
       let binders_ast,argsexport =
         List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> Option.map (on_snd interp_import_cats) export,i)idl)@argsexport) binders_ast
             ([],[]) in

       let mp, args, sign = Declaremods.Synterp.start_modtype id binders_ast mty_sign in
       let argsexport =
         List.map_filter
           (fun (export,id) ->
             Option.map
               (fun export -> export, vernac_import_mod_syntax export (qualid_of_ident ?loc id) ImportAll) export
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

let vernac_declare_module_syntax export {loc;v=id} binders_ast mty_ast =
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
  let export = Option.map (on_snd interp_import_cats) export in
  Option.iter (fun export -> ignore @@ vernac_import_mod_syntax export (qualid_of_ident id) ImportAll) export;
  mp, export, args, sign

let vernac_include_syntax l = Declaremods.Synterp.declare_include l

let vernac_end_module_syntax export {loc;v=id} =
  let _ = Declaremods.Synterp.end_module () in
  Option.map (fun export -> vernac_import_mod_syntax export (qualid_of_ident ?loc id) ImportAll) export

let vernac_end_segment_syntax ({v=id} as lid) =
  let ss = Lib.Synterp.find_opening_node id in
  match ss with
  | Lib.OpenedModule (false,export,_,_) -> ignore (vernac_end_module_syntax export lid)
  | Lib.OpenedModule (true,_,_,_) -> ignore (Declaremods.Synterp.end_modtype ())
  | Lib.OpenedSection _ -> Lib.Synterp.close_section ()
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

let vernac_require_syntax from export qidl =
  let root = match from with
  | None -> None
  | Some from ->
    let (hd, tl) = Libnames.repr_qualid from in
    Some (Libnames.add_dirpath_suffix hd tl)
  in
  let locate (qid,_) =
    let open Loadpath in
    match locate_qualified_library ?root qid with
    | Ok (dir,f) -> dir, f
    | Error LibUnmappedDir -> raise (UnmappedLibrary (root, qid))
    | Error LibNotFound -> raise (NotFoundLibrary (root, qid))
  in
  let modrefl = List.map locate qidl in
  let lib_resolver = Loadpath.try_locate_absolute_library in
  Library.require_library_syntax_from_dirpath ~lib_resolver modrefl;
  Option.iter (fun (export,cats) ->
      let cats = interp_import_cats cats in
      List.iter2 (fun (m,_) (_,f) ->
          import_module_syntax_with_filter ~export cats (MPfile m) f)
        modrefl qidl)
    export

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) filename

let warn_add_loadpath = CWarnings.create ~name:"add-loadpath-deprecated" ~category:"deprecated"
    (fun () -> strbrk "Commands \"Add LoadPath\" and \"Add Rec LoadPath\" are deprecated." ++ spc () ++
               strbrk "Use command-line \"-Q\" or \"-R\" or put them in your _CoqProject file instead." ++ spc () ++
               strbrk "If \"Add [Rec] LoadPath\" is an important feature for you, please open an issue at" ++ spc () ++
               strbrk "https://github.com/coq/coq/issues" ++ spc () ++ strbrk "and explain your workflow.")

let vernac_add_loadpath ~implicit pdir coq_path =
  let open Loadpath in
  warn_add_loadpath ();
  let pdir = expand pdir in
  add_vo_path { unix_path = pdir; coq_path; has_ml = true; implicit; recursive = true }

let vernac_remove_loadpath path =
  Loadpath.remove_load_path (expand path)
  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path path =
  Mltop.add_ml_dir (expand path)

let vernac_declare_ml_module ~local l =
  let local = Option.default false local in
  let l = List.map expand l in
  Mltop.declare_ml_modules local l

let synterp ?loc ~atts v =
  match v with
  | VernacSynterp v0 ->
    let parseff, e = begin match v0 with
    | VernacReservedNotation (infix, sl) ->
      with_module_locality ~atts vernac_reserved_notation ~infix sl;
      true, EVernacNoop
    | VernacNotation (infix,c,infpl,sc) ->
      let (c, main_data, notation_symbols, ntn, syntax_rules, df) = vernac_notation_syntax ~atts ~infix c infpl in
      true, EVernacNotation (c, main_data, notation_symbols, ntn, syntax_rules, df, sc)
    | VernacDeclareCustomEntry s ->
      with_module_locality ~atts vernac_custom_entry s;
      true, EVernacNoop
    | VernacDefineModule (export,lid,bl,mtys,mexprl) ->
      let export, args, argsexport, expr, sign = vernac_define_module_syntax export lid bl mtys mexprl in
      true, EVernacDefineModule (export,lid,args,argsexport,sign,expr)
    | VernacDeclareModuleType (lid,bl,mtys,mtyo) ->
      let args, argsexport, expr, sign = vernac_declare_module_type_syntax lid bl mtys mtyo in
      true, EVernacDeclareModuleType (lid,args,argsexport,sign,expr)
    | VernacDeclareModule (export,lid,bl,mtyo) ->
      let mp, export, args, sign =
        vernac_declare_module_syntax export lid bl mtyo
      in
      true, EVernacDeclareModule (export,lid,args,sign)
    | VernacInclude in_asts ->
      true, EVernacInclude (vernac_include_syntax in_asts)
    | VernacBeginSection lid ->
      Lib.Synterp.open_section lid.CAst.v;
      true, EVernacBeginSection lid
    | VernacEndSegment lid ->
      vernac_end_segment_syntax lid;
      true, EVernacEndSegment lid
    | VernacRequire (from, export, qidl) ->
      vernac_require_syntax from export qidl;
      true, EVernacRequire (from, export, qidl)
    | VernacImport (export,qidl) ->
      let export, mpl = vernac_import_syntax export qidl in
      true, EVernacImport (export,mpl)
    | VernacAddLoadPath { implicit; physical_path; logical_path } ->
      unsupported_attributes atts;
      vernac_add_loadpath ~implicit physical_path logical_path;
      true, EVernacNoop
    | VernacRemoveLoadPath s ->
      unsupported_attributes atts;
      vernac_remove_loadpath s;
      true, EVernacNoop
    | VernacAddMLPath (s) ->
      unsupported_attributes atts;
      vernac_add_ml_path s;
      true, EVernacNoop
    | VernacDeclareMLModule l ->
      with_locality ~atts vernac_declare_ml_module l;
      true, EVernacNoop
    | VernacSetOption (export,key,v) ->
      let atts = if export then CAst.make ?loc ("export", VernacFlagEmpty) :: atts else atts in
      Vernacoptions.vernac_set_option ~locality:(parse option_locality atts) ~stage:Summary.Stage.Synterp key v;
      true, EVernacSetOption (export,key,v)
    | VernacProofMode mn ->
      unsupported_attributes atts;
      true, EVernacNoop
    | VernacExtend (opn,args) ->
      let parseff, f = Vernacextend.type_vernac ?loc ~atts opn args () in
      parseff, EVernacExtend(f)
    end in
    parseff, VernacSynterp e
  | VernacPure x -> false, VernacPure x

  (* Extensions *)
