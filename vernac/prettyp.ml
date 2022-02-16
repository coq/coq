(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Changed by (and thus parts copyright ©) by Lionel Elie Mamane <lionel@mamane.lu>
 * on May-June 2006 for implementation of abstraction of pretty-printing of objects.
 *)

open Pp
open CErrors
open Util
open CAst
open Names
open Termops
open Declarations
open Environ
open Impargs
open Libobject
open Libnames
open Globnames
open Printer
open Printmod
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type object_pr = {
  print_inductive           : MutInd.t -> UnivNames.univ_name_list option -> Pp.t;
  print_constant_with_infos : Constant.t -> UnivNames.univ_name_list option -> Pp.t;
  print_section_variable    : env -> Evd.evar_map -> variable -> Pp.t;
  print_abbreviation        : env -> abbreviation -> Pp.t;
  print_module              : ModPath.t -> Pp.t;
  print_modtype             : ModPath.t -> Pp.t;
  print_named_decl          : env -> Evd.evar_map -> Constr.named_declaration -> Pp.t;
  print_library_leaf       : env -> Evd.evar_map -> bool -> ModPath.t -> Libobject.t -> Pp.t option;
  print_context             : env -> Evd.evar_map -> bool -> int option -> Lib.library_segment -> Pp.t;
  print_typed_value_in_env  : Environ.env -> Evd.evar_map -> EConstr.constr * EConstr.types -> Pp.t;
  print_eval                : Reductionops.reduction_function -> env -> Evd.evar_map -> Constrexpr.constr_expr -> EConstr.unsafe_judgment -> Pp.t;
}

let gallina_print_module mp = print_module ~with_body:true mp
let gallina_print_modtype = print_modtype

(**************)
(** Utilities *)

let print_closed_sections = ref false

let pr_infos_list l = v 0 (prlist_with_sep cut (fun x -> x) l)

let with_line_skip l = if List.is_empty l then mt() else fnl() ++ fnl () ++ pr_infos_list l

let blankline = mt() (* add a blank sentence in the list of infos *)

let add_colon prefix = if ismt prefix then mt () else prefix ++ str ": "

let int_or_no n = if Int.equal n 0 then str "no" else int n

(*******************)
(** Basic printing *)

let print_basename sp = pr_global (GlobRef.ConstRef sp)

let print_ref reduce ref udecl =
  let env = Global.env () in
  let typ, univs = Typeops.type_of_global_in_context env ref in
  let inst = Univ.make_abstract_instance univs in
  let bl = Printer.universe_binders_with_opt_names (Environ.universes_of_global env ref) udecl in
  let sigma = Evd.from_ctx (UState.of_binders bl) in
  let typ =
    if reduce then
      let ctx,ccl = Reductionops.splay_prod_assum env sigma (EConstr.of_constr typ)
      in EConstr.to_constr sigma (EConstr.it_mkProd_or_LetIn ccl ctx)
    else typ in
  let typ = Arguments_renaming.rename_type typ ref in
  let impargs = select_stronger_impargs (implicits_of_global ref) in
  let impargs = List.map binding_kind_of_status impargs in
  let variance = let open GlobRef in match ref with
    | VarRef _ | ConstRef _ -> None
    | IndRef (ind,_) | ConstructRef ((ind,_),_) ->
      let mind = Environ.lookup_mind ind env in
      mind.Declarations.mind_variance
  in
  let inst =
    if Global.is_polymorphic ref
    then Printer.pr_universe_instance sigma inst
    else mt ()
  in
  let priv = None in (* We deliberately don't print private univs in About. *)
  hov 0 (pr_global ref ++ inst ++ str " :" ++ spc () ++ pr_ltype_env env sigma ~impargs typ ++
         Printer.pr_abstract_universe_ctx sigma ?variance univs ?priv)

(********************************)
(** Printing implicit arguments *)

let pr_impl_name imp = Id.print (name_of_implicit imp)

let print_impargs_by_name max = function
  | []  -> []
  | impls ->
     let n = List.length impls in
     [hov 0 (str (String.plural n "Argument") ++ spc() ++
      prlist_with_sep pr_comma pr_impl_name impls ++ spc() ++
      str (String.conjugate_verb_to_be n) ++ str" implicit" ++
      (if max then strbrk " and maximally inserted" else mt()))]

let print_one_impargs_list l =
  let imps = List.filter is_status_implicit l in
  let maximps = List.filter Impargs.maximal_insertion_of imps in
  let nonmaximps = List.subtract (=) imps maximps in (* FIXME *)
  print_impargs_by_name false nonmaximps @
  print_impargs_by_name true maximps

let print_impargs_list prefix l =
  let l = extract_impargs_data l in
  List.flatten (List.map (fun (cond,imps) ->
    match cond with
    | None ->
        List.map (fun pp -> add_colon prefix ++ pp)
          (print_one_impargs_list imps)
    | Some (n1,n2) ->
       [v 2 (prlist_with_sep cut (fun x -> x)
         [(if ismt prefix then str "When" else prefix ++ str ", when") ++
           str " applied to " ++
           (if Int.equal n1 n2 then int_or_no n2 else
            if Int.equal n1 0 then str "no more than " ++ int n2
            else int n1 ++ str " to " ++ int_or_no n2) ++
            str (String.plural n2 " argument") ++ str ":";
          v 0 (prlist_with_sep cut (fun x -> x)
            (if List.exists is_status_implicit imps
            then print_one_impargs_list imps
            else [str "No implicit arguments"]))])]) l)

let need_expansion impl ref =
  let typ, _ = Typeops.type_of_global_in_context (Global.env ()) ref in
  let ctx = Term.prod_assum typ in
  let nprods = List.count is_local_assum ctx in
  not (List.is_empty impl) && List.length impl >= nprods &&
    let _,lastimpl = List.chop nprods impl in
      List.exists is_status_implicit lastimpl

let print_impargs ref =
  let ref = Smartlocate.smart_global ref in
  let impl = implicits_of_global ref in
  let has_impl = not (List.is_empty impl) in
  (* Need to reduce since implicits are computed with products flattened *)
  pr_infos_list
    ([ print_ref (need_expansion (select_impargs_size 0 impl) ref) ref None;
       blankline ] @
    (if has_impl then print_impargs_list (mt()) impl
     else [str "No implicit arguments"]))

(*********************)
(** Printing Opacity *)

type opacity =
  | FullyOpaque
  | TransparentMaybeOpacified of Conv_oracle.level

let opacity env =
  function
  | GlobRef.VarRef v when NamedDecl.is_local_def (Environ.lookup_named v env) ->
      Some(TransparentMaybeOpacified
        (Conv_oracle.get_strategy (Environ.oracle env) (VarKey v)))
  | GlobRef.ConstRef cst ->
      let cb = Environ.lookup_constant cst env in
      (match cb.const_body with
        | Undef _ | Primitive _ -> None
        | OpaqueDef _ -> Some FullyOpaque
        | Def _ -> Some
          (TransparentMaybeOpacified
            (Conv_oracle.get_strategy (Environ.oracle env) (ConstKey cst))))
  | _ -> None

let print_opacity ref =
  match opacity (Global.env()) ref with
    | None -> []
    | Some s ->
       [pr_global ref ++ str " is " ++
        match s with
          | FullyOpaque -> str "opaque"
          | TransparentMaybeOpacified Conv_oracle.Opaque ->
              str "basically transparent but considered opaque for reduction"
          | TransparentMaybeOpacified lev when Conv_oracle.is_transparent lev ->
              str "transparent"
          | TransparentMaybeOpacified (Conv_oracle.Level n) ->
              str "transparent (with expansion weight " ++ int n ++ str ")"
          | TransparentMaybeOpacified Conv_oracle.Expand ->
              str "transparent (with minimal expansion weight)"]

(*******************)

let print_if_is_coercion ref =
  if Coercionops.coercion_exists ref then
    let i = Coercionops.coercion_info ref in
    let r = if i.Coercionops.coe_reversible then " reversible" else "" in
    [pr_global ref ++ str " is a" ++ str r ++ str " coercion"]
  else []

(*******************)
(* *)

let pr_template_variables = function
  | [] -> mt ()
  | vars -> str " on " ++ prlist_with_sep spc UnivNames.(pr_with_global_universes empty_binders) vars

let print_polymorphism ref =
  let poly = Global.is_polymorphic ref in
  let template_poly = Global.is_template_polymorphic ref in
  let template_variables = Global.get_template_polymorphic_variables ref in
  [ pr_global ref ++ str " is " ++
      (if poly then str "universe polymorphic"
       else if template_poly then
         str "template universe polymorphic"
         ++ if !Detyping.print_universes then h (pr_template_variables template_variables) else mt()
       else str "not universe polymorphic") ]

let print_type_in_type ref =
  let unsafe = Global.is_type_in_type ref in
  if unsafe then
    [ pr_global ref ++ str " relies on an unsafe universe hierarchy"]
  else []

let print_primitive_record recflag mipv = function
  | PrimRecord _ ->
    let eta = match recflag with
    | CoFinite | Finite -> str" without eta conversion"
    | BiFinite -> str " with eta conversion"
    in
    [Id.print mipv.(0).mind_typename ++ str" has primitive projections" ++ eta ++ str"."]
  | FakeRecord | NotRecord -> []

let print_primitive ref =
  match ref with
  | GlobRef.IndRef ind ->
    let mib,_ = Global.lookup_inductive ind in
      print_primitive_record mib.mind_finite mib.mind_packets mib.mind_record
  | _ -> []

let needs_extra_scopes ref scopes =
  let open Constr in
  let rec aux env t = function
    | [] -> false
    | _::scopes -> match kind (Reduction.whd_all env t) with
      | Prod (na,dom,codom) -> aux (push_rel (RelDecl.LocalAssum (na,dom)) env) codom scopes
      | _ -> true
  in
  let env = Global.env() in
  let ty, _ctx = Typeops.type_of_global_in_context env ref in
  aux env ty scopes

let implicit_kind_of_status = function
  | None -> Anonymous, Glob_term.Explicit
  | Some ((na,_,_),_,(maximal,_)) -> na, if maximal then Glob_term.MaxImplicit else Glob_term.NonMaxImplicit

let extra_implicit_kind_of_status imp =
  let _,imp = implicit_kind_of_status imp in
  (Anonymous, imp)

let dummy = {
  Vernacexpr.implicit_status = Glob_term.Explicit;
   name = Anonymous;
   recarg_like = false;
   notation_scope = None;
 }

let is_dummy = function
  | Vernacexpr.(RealArg {implicit_status; name; recarg_like; notation_scope}) ->
    name = Anonymous && not recarg_like && notation_scope = None && implicit_status = Glob_term.Explicit
  | _ -> false

let rec main_implicits i renames recargs scopes impls =
  if renames = [] && recargs = [] && scopes = [] && impls = [] then []
  else
    let recarg_like, recargs = match recargs with
      | j :: recargs when i = j -> true, recargs
      | _ -> false, recargs
    in
    let (name, implicit_status) =
      match renames, impls with
      | _, (Some _ as i) :: _ -> implicit_kind_of_status i
      | name::_, _ -> (name,Glob_term.Explicit)
      | [], (None::_ | []) -> (Anonymous, Glob_term.Explicit)
    in
    let notation_scope = match scopes with
      | scope :: _ -> Option.map CAst.make scope
      | [] -> None
    in
    let status = {Vernacexpr.implicit_status; name; recarg_like; notation_scope} in
    let tl = function [] -> [] | _::tl -> tl in
    (* recargs is special -> tl handled above *)
    let rest = main_implicits (i+1) (tl renames) recargs (tl scopes) (tl impls) in
    status :: rest

let rec insert_fake_args volatile bidi impls =
  let open Vernacexpr in
  match volatile, bidi with
  | Some 0, _ -> VolatileArg :: insert_fake_args None bidi impls
  | _, Some 0 -> BidiArg :: insert_fake_args volatile None impls
  | None, None -> List.map (fun a -> RealArg a) impls
  | _, _ ->
    let hd, tl = match impls with
      | impl :: impls -> impl, impls
      | [] -> dummy, []
    in
    let f = Option.map pred in
    RealArg hd :: insert_fake_args (f volatile) (f bidi) tl

let print_arguments ref =
  let qid = Nametab.shortest_qualid_of_global Id.Set.empty ref in
  let flags, recargs, nargs_for_red =
    let open Reductionops.ReductionBehaviour in
    match get ref with
    | None -> [], [], None
    | Some NeverUnfold -> [`ReductionNeverUnfold], [], None
    | Some (UnfoldWhen { nargs; recargs }) -> [], recargs, nargs
    | Some (UnfoldWhenNoMatch { nargs; recargs }) -> [`ReductionDontExposeCase], recargs, nargs
  in
  let names, not_renamed =
    try Arguments_renaming.arguments_names ref, false
    with Not_found ->
      let env = Global.env () in
      let ty, _ = Typeops.type_of_global_in_context env ref in
      List.map pi1 (Impargs.compute_implicits_names env (Evd.from_env env) (EConstr.of_constr ty)), true in
  let scopes = Notation.find_arguments_scope ref in
  let flags = if needs_extra_scopes ref scopes then `ExtraScopes::flags else flags in
  let impls = Impargs.extract_impargs_data (Impargs.implicits_of_global ref) in
  let impls, moreimpls = match impls with
    | (_, impls) :: rest -> impls, rest
    | [] -> assert false
  in
  let impls = main_implicits 0 names recargs scopes impls in
  let moreimpls = List.map (fun (_,i) -> List.map extra_implicit_kind_of_status i) moreimpls in
  let bidi = Pretyping.get_bidirectionality_hint ref in
  let impls = insert_fake_args nargs_for_red bidi impls in
  if List.for_all is_dummy impls && moreimpls = [] && flags = [] then []
  else
    let open Constrexpr in
    let open Vernacexpr in
    [Ppvernac.pr_vernac_expr
       (VernacArguments (CAst.make (AN qid), impls, moreimpls, flags)) ++
     (if not_renamed then mt () else
      fnl () ++ str "  (where some original arguments have been renamed)")]

let print_name_infos ref =
  let type_info_for_implicit =
    if need_expansion (select_impargs_size 0 (implicits_of_global ref)) ref then
      (* Need to reduce since implicits are computed with products flattened *)
      [str "Expanded type for implicit arguments";
       print_ref true ref None; blankline]
    else
      [] in
  print_type_in_type ref @
  print_primitive ref @
  type_info_for_implicit @
  print_arguments ref @
  print_if_is_coercion ref

let print_inductive_args sp mipv =
  let flatmapi f v = List.flatten (Array.to_list (Array.mapi f v)) in
  flatmapi
    (fun i mip -> print_arguments (GlobRef.IndRef (sp,i)) @
                  flatmapi (fun j _ -> print_arguments (GlobRef.ConstructRef ((sp,i),j+1)))
                    mip.mind_consnames) mipv

let print_bidi_hints gr =
  match Pretyping.get_bidirectionality_hint gr with
  | None -> []
  | Some nargs ->
    [str "Using typing information from context after typing the " ++ int nargs ++ str " first arguments"]

(*********************)
(* "Locate" commands *)

type 'a locatable_info = {
  locate : qualid -> 'a option;
  locate_all : qualid -> 'a list;
  shortest_qualid : 'a -> qualid;
  name : 'a -> Pp.t;
  print : 'a -> Pp.t;
  about : 'a -> Pp.t;
}

type locatable = Locatable : 'a locatable_info -> locatable

type logical_name =
  | Term of GlobRef.t
  | Dir of Nametab.GlobDirRef.t
  | Abbreviation of abbreviation
  | Module of ModPath.t
  | ModuleType of ModPath.t
  | Other : 'a * 'a locatable_info -> logical_name
  | Undefined of qualid

(** Generic table for objects that are accessible through a name. *)
let locatable_map : locatable String.Map.t ref = ref String.Map.empty

let register_locatable name f =
  locatable_map := String.Map.add name (Locatable f) !locatable_map

exception ObjFound of logical_name

let locate_any_name qid =
  try Term (Nametab.locate qid)
  with Not_found ->
  try Abbreviation (Nametab.locate_abbreviation qid)
  with Not_found ->
  try Dir (Nametab.locate_dir qid)
  with Not_found ->
  try Module (Nametab.locate_module qid)
  with Not_found ->
  try ModuleType (Nametab.locate_modtype qid)
  with Not_found ->
    let iter _ (Locatable info) = match info.locate qid with
    | None -> ()
    | Some ans -> raise (ObjFound (Other (ans, info)))
    in
    try String.Map.iter iter !locatable_map; Undefined qid
    with ObjFound obj -> obj

let pr_located_qualid = function
  | Term ref ->
      let ref_str = let open GlobRef in match ref with
          ConstRef _ -> "Constant"
        | IndRef _ -> "Inductive"
        | ConstructRef _ -> "Constructor"
        | VarRef _ -> "Variable" in
      str ref_str ++ spc () ++ pr_path (Nametab.path_of_global ref)
  | Abbreviation kn ->
      str "Notation" ++ spc () ++ pr_path (Nametab.path_of_abbreviation kn)
  | Dir dir ->
      let s,dir =
        let open Nametab in
        let open GlobDirRef in match dir with
        | DirOpenModule { obj_dir ; _ } -> "Open Module", obj_dir
        | DirOpenModtype { obj_dir ; _ } -> "Open Module Type", obj_dir
        | DirOpenSection { obj_dir ; _ } -> "Open Section", obj_dir
      in
      str s ++ spc () ++ DirPath.print dir
  | Module mp ->
    str "Module" ++ spc () ++ DirPath.print (Nametab.dirpath_of_module mp)
  | ModuleType mp ->
      str "Module Type" ++ spc () ++ pr_path (Nametab.path_of_modtype mp)
  | Other (obj, info) -> info.name obj
  | Undefined qid ->
      pr_qualid qid ++ spc () ++ str "not a defined object."

let canonize_ref = let open GlobRef in function
  | ConstRef c ->
    let kn = Constant.canonical c in
    if KerName.equal (Constant.user c) kn then None
    else Some (ConstRef (Constant.make1 kn))
  | IndRef (ind,i) ->
    let kn = MutInd.canonical ind in
    if KerName.equal (MutInd.user ind) kn then None
    else Some (IndRef (MutInd.make1 kn, i))
  | ConstructRef ((ind,i),j) ->
    let kn = MutInd.canonical ind in
    if KerName.equal (MutInd.user ind) kn then None
    else Some (ConstructRef ((MutInd.make1 kn, i),j))
  | VarRef _ -> None

let display_alias = function
  | Term r ->
    begin match canonize_ref r with
    | None -> mt ()
    | Some r' ->
      let q' = Nametab.shortest_qualid_of_global Id.Set.empty r' in
      spc () ++ str "(alias of " ++ pr_qualid q' ++ str ")"
    end
  | _ -> mt ()

let locate_term qid =
  let expand = function
    | TrueGlobal ref ->
        Term ref, Nametab.shortest_qualid_of_global Id.Set.empty ref
    | Abbrev kn ->
        Abbreviation kn, Nametab.shortest_qualid_of_abbreviation Id.Set.empty kn
  in
  List.map expand (Nametab.locate_extended_all qid)

let locate_module qid =
  let all = Nametab.locate_extended_all_module qid in
  let map mp = Module mp, Nametab.shortest_qualid_of_module mp in
  let mods = List.map map all in
  (* Don't forget the opened modules: they are not part of the same name tab. *)
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = let open Nametab.GlobDirRef in match dir with
  | DirOpenModule _ -> Some (Dir dir, qid)
  | _ -> None
  in
  mods @ List.map_filter map all

let locate_modtype qid =
  let all = Nametab.locate_extended_all_modtype qid in
  let map mp = ModuleType mp, Nametab.shortest_qualid_of_modtype mp in
  let modtypes = List.map map all in
  (* Don't forget the opened module types: they are not part of the same name tab. *)
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = let open Nametab.GlobDirRef in match dir with
  | DirOpenModtype _ -> Some (Dir dir, qid)
  | _ -> None
  in
  modtypes @ List.map_filter map all

let locate_other s qid =
  let Locatable info = String.Map.find s !locatable_map in
  let ans = info.locate_all qid in
  let map obj = (Other (obj, info), info.shortest_qualid obj) in
  List.map map ans

type locatable_kind =
| LocTerm
| LocModule
| LocOther of string
| LocAny

let print_located_qualid name flags qid =
  let located = match flags with
  | LocTerm -> locate_term qid
  | LocModule -> locate_modtype qid @ locate_module qid
  | LocOther s -> locate_other s qid
  | LocAny ->
    locate_term qid @
    locate_modtype qid @
    locate_module qid @
    String.Map.fold (fun s _ accu -> locate_other s qid @ accu) !locatable_map []
  in
  match located with
    | [] ->
        let (dir,id) = repr_qualid qid in
        if DirPath.is_empty dir then
          str "No " ++ str name ++ str " of basename" ++ spc () ++ Id.print id
        else
          str "No " ++ str name ++ str " of suffix" ++ spc () ++ pr_qualid qid
    | l ->
        prlist_with_sep fnl
        (fun (o,oqid) ->
          hov 2 (pr_located_qualid o ++
          (if not (qualid_eq oqid qid) then
            spc() ++ str "(shorter name to refer to it in current context is "
            ++ pr_qualid oqid ++ str")"
           else mt ()) ++
          display_alias o)) l

let print_located_term ref = print_located_qualid "term" LocTerm ref
let print_located_other s ref = print_located_qualid s (LocOther s) ref
let print_located_module ref = print_located_qualid "module" LocModule ref
let print_located_qualid ref = print_located_qualid "object" LocAny ref

(******************************************)
(**** Printing declarations and judgments *)
(****  Gallina layer                  *****)

let gallina_print_typed_value_in_env env sigma (trm,typ) =
  (pr_leconstr_env ~inctx:true env sigma trm ++ fnl () ++
     str "     : " ++ pr_letype_env env sigma typ)

(* To be improved; the type should be used to provide the types in the
   abstractions. This should be done recursively inside pr_lconstr, so that
   the pretty-print of a proposition (P:(nat->nat)->Prop)(P [u]u)
   synthesizes the type nat of the abstraction on u *)

let print_named_def env sigma name body typ =
  let pbody = pr_lconstr_env ~inctx:true env sigma body in
  let ptyp = pr_ltype_env env sigma typ in
  let pbody = if Constr.isCast body then surround pbody else pbody in
  (str "*** [" ++ str name ++ str " " ++
     hov 0 (str ":=" ++ brk (1,2) ++ pbody ++ spc () ++
              str ":" ++ brk (1,2) ++ ptyp) ++
           str "]")

let print_named_assum env sigma name typ =
  str "*** [" ++ str name ++ str " : " ++ pr_ltype_env env sigma typ ++ str "]"

let gallina_print_named_decl env sigma =
  let open Context.Named.Declaration in
  function
  | LocalAssum (id, typ) ->
     print_named_assum env sigma (Id.to_string id.Context.binder_name) typ
  | LocalDef (id, body, typ) ->
     print_named_def env sigma (Id.to_string id.Context.binder_name) body typ

let assumptions_for_print lna =
  List.fold_right (fun na env -> add_name na env) lna empty_names_context

(*********************)
(* *)

let gallina_print_inductive sp udecl =
  let env = Global.env() in
  let mib = Environ.lookup_mind sp env in
  let mipv = mib.mind_packets in
  pr_mutual_inductive_body env sp mib udecl ++
  with_line_skip
    (print_primitive_record mib.mind_finite mipv mib.mind_record @
     print_inductive_args sp mipv)

let print_named_decl env sigma id =
  gallina_print_named_decl env sigma (Global.lookup_named id) ++ fnl ()

let gallina_print_section_variable env sigma id =
  print_named_decl env sigma id ++
  with_line_skip (print_name_infos (GlobRef.VarRef id))

let print_body env evd = function
  | Some c  -> pr_lconstr_env ~inctx:true env evd c
  | None -> (str"<no body>")

let print_typed_body env evd (val_0,typ) =
  (print_body env evd val_0 ++ fnl () ++ str "     : " ++ pr_ltype_env env evd typ)

let print_instance sigma cb =
  if Declareops.constant_is_polymorphic cb then
    let univs = Declareops.constant_polymorphic_context cb in
    let inst = Univ.make_abstract_instance univs in
    pr_universe_instance sigma inst
  else mt()

let print_constant with_values sep sp udecl =
  let cb = Global.lookup_constant sp in
  let val_0 = Global.body_of_constant_body Library.indirect_accessor cb in
  let typ = cb.const_type in
  let univs = cb.const_universes in
  let uctx =
    UState.of_binders
      (Printer.universe_binders_with_opt_names (Declareops.constant_polymorphic_context cb) udecl)
  in
  let env = Global.env () and sigma = Evd.from_ctx uctx in
  let pr_ltype = pr_ltype_env env sigma in
  hov 0 (
    match val_0 with
    | None ->
        str"*** [ " ++
        print_basename sp ++ print_instance sigma cb ++ str " : " ++ cut () ++ pr_ltype typ ++
        str" ]" ++
        Printer.pr_universes sigma univs
    | Some (c, priv, ctx) ->
      let priv = match priv with
      | Opaqueproof.PrivateMonomorphic () -> None
      | Opaqueproof.PrivatePolymorphic ctx -> Some ctx
      in
        print_basename sp ++ print_instance sigma cb ++ str sep ++ cut () ++
        (if with_values then print_typed_body env sigma (Some c,typ) else pr_ltype typ)++
        Printer.pr_universes sigma univs ?priv)

let gallina_print_constant_with_infos sp udecl =
  print_constant true " = " sp udecl ++
  with_line_skip (print_name_infos (GlobRef.ConstRef sp))

let gallina_print_abbreviation env kn =
  let qid = Nametab.shortest_qualid_of_abbreviation Id.Set.empty kn
  and (vars,a) = Abbreviation.search_abbreviation kn in
  let c = Notation_ops.glob_constr_of_notation_constr a in
  hov 2
    (hov 4
       (str "Notation " ++ pr_qualid qid ++
        prlist (fun id -> spc () ++ Id.print id) (List.map fst vars) ++
        spc () ++ str ":=") ++
     spc () ++
     Constrextern.without_specific_symbols
       [Notation_term.AbbrevRule kn] (pr_glob_constr_env env (Evd.from_env env)) c)

module DynHandle = Libobject.Dyn.Map(struct type 'a t = 'a -> Pp.t option end)

let handle h (Libobject.Dyn.Dyn (tag, o)) = match DynHandle.find tag h with
| f -> f o
| exception Not_found -> None

(* TODO: this kind of feature should not rely on the Libobject stack. There is
   no reason that an object in the stack corresponds to a user-facing
   declaration. It may have been so at the time this was written, but this
   needs to be done in a more principled way. *)
let gallina_print_library_leaf env sigma with_values mp lobj =
  let sep = if with_values then " = " else " : " in
  match lobj with
  | AtomicObject o ->
    let handler =
      DynHandle.add Declare.Internal.objVariable begin fun id ->
          (* Outside sections, VARIABLES still exist but only with universes
             constraints *)
          (try Some(print_named_decl env sigma id) with Not_found -> None)
      end @@
      DynHandle.add Declare.Internal.Constant.tag begin fun (id,_) ->
        let kn = Constant.make2 mp (Label.of_id id) in
        Some (print_constant with_values sep kn None)
      end @@
      DynHandle.add DeclareInd.Internal.objInductive begin fun (id,_) ->
        let kn = MutInd.make2 mp (Label.of_id id) in
        Some (gallina_print_inductive kn None)
      end @@
      DynHandle.empty
    in
    handle handler o
  | ModuleObject (id,_) ->
    Some (print_module ~with_body:with_values (MPdot (mp,Label.of_id id)))
  | ModuleTypeObject (id,_) ->
    Some (print_modtype (MPdot (mp, Label.of_id id)))
  | IncludeObject _ | KeepObject _ | ExportObject _ -> None

let decr = Option.map ((+) (-1))

let is_done = Option.equal Int.equal (Some 0)

let print_leaves env sigma with_values mp =
  let rec prec n = function
    | [] -> n, mt()
    | o :: rest ->
      if is_done n then n, mt()
      else begin match gallina_print_library_leaf env sigma with_values mp o with
        | Some pp ->
          let n, prest = prec (decr n) rest in
          n, prest ++ pp
        | None -> prec n rest
      end
  in
  prec

let gallina_print_context env sigma with_values =
  let rec prec n = function
    | [] -> mt()
    | (node, leaves) :: rest ->
      if is_done n then mt()
      else
        let mp = (Lib.node_prefix node).Nametab.obj_mp in
        let n, pleaves = print_leaves env sigma with_values mp n leaves in
        if is_done n then pleaves
        else prec n rest ++ pleaves
  in
  prec

let pr_prefix_name prefix = Id.print (snd (split_dirpath prefix.Nametab.obj_dir))

let print_library_node = function
  | Lib.OpenedSection (prefix, _) ->
    str " >>>>>>> Section " ++ pr_prefix_name prefix
  | Lib.OpenedModule (_,_,prefix,_) ->
    str " >>>>>>> Module " ++ pr_prefix_name prefix
  | Lib.CompilingLibrary { Nametab.obj_dir; _ } ->
    str " >>>>>>> Library " ++ DirPath.print obj_dir

let gallina_print_eval red_fun env sigma _ {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env sigma trm in
  (str "     = " ++ gallina_print_typed_value_in_env env sigma (ntrm,typ))

(******************************************)
(**** Printing abstraction layer          *)

let default_object_pr = {
  print_inductive           = gallina_print_inductive;
  print_constant_with_infos = gallina_print_constant_with_infos;
  print_section_variable    = gallina_print_section_variable;
  print_abbreviation        = gallina_print_abbreviation;
  print_module              = gallina_print_module;
  print_modtype             = gallina_print_modtype;
  print_named_decl          = gallina_print_named_decl;
  print_library_leaf        = gallina_print_library_leaf;
  print_context             = gallina_print_context;
  print_typed_value_in_env  = gallina_print_typed_value_in_env;
  print_eval                = gallina_print_eval;
}

let object_pr = ref default_object_pr
let set_object_pr = (:=) object_pr

let print_inductive x = !object_pr.print_inductive x
let print_constant_with_infos c = !object_pr.print_constant_with_infos c
let print_section_variable c = !object_pr.print_section_variable c
let print_abbreviation x = !object_pr.print_abbreviation x
let print_module x  = !object_pr.print_module  x
let print_modtype x = !object_pr.print_modtype x
let print_named_decl x = !object_pr.print_named_decl x
let print_library_leaf x = !object_pr.print_library_leaf x
let print_context x = !object_pr.print_context x
let print_typed_value_in_env x = !object_pr.print_typed_value_in_env x
let print_eval x = !object_pr.print_eval x

(******************************************)
(**** Printing declarations and judgments *)
(****  Abstract layer                 *****)

let print_judgment env sigma {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env sigma (trm, typ)

let print_safe_judgment env sigma j =
  let trm = Safe_typing.j_val j in
  let typ = Safe_typing.j_type j in
  let trm = EConstr.of_constr trm in
  let typ = EConstr.of_constr typ in
  print_typed_value_in_env env sigma (trm, typ)

(*********************)
(* *)

let print_full_context env sigma =
  print_context env sigma true None (Lib.contents ())
let print_full_context_typ env sigma =
  print_context env sigma false None (Lib.contents ())

module DynHandleF = Libobject.Dyn.Map(struct type 'a t = 'a -> Pp.t end)

let handleF h (Libobject.Dyn.Dyn (tag, o)) = match DynHandleF.find tag h with
| f -> f o
| exception Not_found -> mt ()

(* TODO: see the comment for {!gallina_print_leaf_entry} *)
let print_full_pure_atomic env sigma mp lobj =
  let handler =
    DynHandleF.add Declare.Internal.Constant.tag begin fun (id,_) ->
      let kn = KerName.make mp (Label.of_id id) in
      let con = Global.constant_of_delta_kn kn in
      let cb = Global.lookup_constant con in
      let typ = cb.const_type in
      hov 0 (
        match cb.const_body with
        | Undef _ ->
          str "Parameter " ++
          print_basename con ++ str " : " ++ cut () ++ pr_ltype_env env sigma typ
        | OpaqueDef lc ->
          str "Theorem " ++ print_basename con ++ cut () ++
          str " : " ++ pr_ltype_env env sigma typ ++ str "." ++ fnl () ++
          str "Proof " ++ pr_lconstr_env env sigma
            (fst (Global.force_proof Library.indirect_accessor lc))
        | Def c ->
          str "Definition " ++ print_basename con ++ cut () ++
          str "  : " ++ pr_ltype_env env sigma typ ++ cut () ++ str " := " ++
          pr_lconstr_env env sigma c
        | Primitive _ ->
          str "Primitive " ++
          print_basename con ++ str " : " ++ cut () ++ pr_ltype_env env sigma typ)
      ++ str "." ++ fnl () ++ fnl ()
    end @@
    DynHandleF.add DeclareInd.Internal.objInductive begin fun (id,_) ->
      let kn = KerName.make mp (Label.of_id id) in
      let mind = Global.mind_of_delta_kn kn in
      let mib = Global.lookup_mind mind in
      pr_mutual_inductive_body (Global.env()) mind mib None ++
      str "." ++ fnl () ++ fnl ()
    end @@
    DynHandleF.empty
  in
  handleF handler lobj

let print_full_pure_leaf env sigma mp = function
  | AtomicObject lobj -> print_full_pure_atomic env sigma mp lobj
  | ModuleObject (id, _) ->
    (* TODO: make it reparsable *)
    print_module (MPdot (mp,Label.of_id id)) ++ str "." ++ fnl () ++ fnl ()
  | ModuleTypeObject (id, _) ->
    (* TODO: make it reparsable *)
    print_modtype (MPdot (mp,Label.of_id id)) ++ str "." ++ fnl () ++ fnl ()
  | _ -> mt()

let print_full_pure_context env sigma =
  let rec prec = function
    | (node,leaves)::rest ->
      let mp = (Lib.node_prefix node).Nametab.obj_mp in
      let pp = Pp.prlist (print_full_pure_leaf env sigma mp) leaves in
      prec rest ++ pp
  | [] -> mt ()
  in
  prec (Lib.contents ())

(* For printing an inductive definition with
   its constructors and elimination,
   assume that the declaration of constructors and eliminations
   follows the definition of the inductive type *)

(* This is designed to print the contents of an opened section *)
let read_sec_context qid =
  let dir =
    try Nametab.locate_section qid
    with Not_found ->
      user_err ?loc:qid.loc (str "Unknown section.") in
  let rec get_cxt in_cxt = function
    | (Lib.OpenedSection ({Nametab.obj_dir;_},_), _ as hd)::rest ->
        if DirPath.equal dir obj_dir then (hd::in_cxt) else get_cxt (hd::in_cxt) rest
    | [] -> []
    | hd::rest -> get_cxt (hd::in_cxt) rest
  in
  let cxt = Lib.contents () in
  List.rev (get_cxt [] cxt)

let print_sec_context env sigma sec =
  print_context env sigma true None (read_sec_context sec)

let print_sec_context_typ env sigma sec =
  print_context env sigma false None (read_sec_context sec)

let maybe_error_reject_univ_decl na udecl =
  let open GlobRef in
  match na, udecl with
  | _, None | Term (ConstRef _ | IndRef _ | ConstructRef _), Some _ -> ()
  | (Term (VarRef _) | Abbreviation _ | Dir _ | Module _ | ModuleType _ | Other _ | Undefined _), Some udecl ->
    (* TODO Print na somehow *)
    user_err (str "This object does not support universe names.")

let print_any_name env sigma na udecl =
  maybe_error_reject_univ_decl na udecl;
  let open GlobRef in
  match na with
  | Term (ConstRef sp) -> print_constant_with_infos sp udecl
  | Term (IndRef (sp,_)) -> print_inductive sp udecl
  | Term (ConstructRef ((sp,_),_)) -> print_inductive sp udecl
  | Term (VarRef sp) -> print_section_variable env sigma sp
  | Abbreviation kn -> print_abbreviation env kn
  | Module mp -> print_module mp
  | Dir _ -> mt ()
  | ModuleType mp -> print_modtype mp
  | Other (obj, info) -> info.print obj
  | Undefined qid ->
  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
    let dir,str = repr_qualid qid in
    if not (DirPath.is_empty dir) then raise Not_found;
    str |> Global.lookup_named |> print_named_decl env sigma

  with Not_found -> user_err ?loc:qid.loc (pr_qualid qid ++ spc () ++ str "not a defined object.")

let print_name env sigma na udecl =
  match na with
  | {loc; v=Constrexpr.ByNotation (ntn,sc)} ->
    print_any_name env sigma
      (Term (Notation.interp_notation_as_global_reference ?loc ~head:false (fun _ -> true)
               ntn sc))
      udecl
  | {loc; v=Constrexpr.AN ref} ->
    print_any_name env sigma (locate_any_name ref) udecl

let print_notation_grammar env sigma ntn =
  let ng = List.hd (Notgram_ops.grammar_of_notation ntn) in
  let assoc = ng.Notation_gram.notgram_assoc in
  let prdf () = Pp.str "no associativity" in
  Pp.(pr_opt_no_spc_default prdf Gramlib.Gramext.pr_assoc assoc)

exception PrintNotationNotFound of Constrexpr.notation_entry * string

let () = CErrors.register_handler @@ function
  | PrintNotationNotFound (entry, ntn_str) ->
      let entry_string = match entry with
      | Constrexpr.InConstrEntry -> "."
      | Constrexpr.InCustomEntry e -> " in " ^ e ^ " entry."
      in
      Some Pp.(str "\"" ++ str ntn_str ++ str "\"" ++ spc ()
        ++ str "cannot be interpreted as a known notation" ++ str entry_string ++ spc ()
        ++ strbrk "Make sure that symbols are surrounded by spaces and that holes are explicitly denoted by \"_\".")
  | _ -> None

let error_print_notation_not_found e s =
  raise @@ PrintNotationNotFound (e, s)

let print_notation env sigma entry raw_ntn =
  (* make sure entry exists *)
  let () =
    match entry with
    | Constrexpr.InConstrEntry -> ()
    | Constrexpr.InCustomEntry e -> Metasyntax.check_custom_entry e
  in
  (* convert notation string to key. eg. "x + y" to "_ + _" *)
  let interp_ntn = Notation.interpret_notation_string raw_ntn in
  let ntn = (entry, interp_ntn) in
  try
    let lvl = Notation.level_of_notation ntn in
    let args = Notgram_ops.subentries_of_notation ntn in
    let pplvl = Metasyntax.pr_level ntn lvl args in
    Pp.(str "Notation \"" ++ str interp_ntn ++ str "\"" ++ spc ()
      ++ pplvl ++ pr_comma () ++ print_notation_grammar env sigma ntn
      ++ str ".")
  with Not_found -> error_print_notation_not_found entry raw_ntn

let print_opaque_name env sigma qid =
  let open GlobRef in
  match Nametab.global qid with
    | ConstRef cst ->
      let cb = Global.lookup_constant cst in
      if Declareops.constant_has_body cb then
        print_constant_with_infos cst None
      else
        user_err Pp.(str "Not a defined constant.")
    | IndRef (sp,_) ->
      print_inductive sp None
    | ConstructRef cstr as gr ->
      let ty, ctx = Typeops.type_of_global_in_context env gr in
      let ty = EConstr.of_constr ty in
      let open EConstr in
      print_typed_value_in_env env sigma (mkConstruct cstr, ty)
    | VarRef id ->
      env |> lookup_named id |> print_named_decl env sigma

let print_about_any ?loc env sigma k udecl =
  maybe_error_reject_univ_decl k udecl;
  match k with
  | Term ref ->
    let rb = Reductionops.ReductionBehaviour.print ref in
    Dumpglob.add_glob ?loc ref;
      pr_infos_list
       (print_ref false ref udecl :: blankline ::
        print_polymorphism ref @
        print_name_infos ref @
        (if Pp.ismt rb then [] else [rb]) @
        print_opacity ref @
  print_bidi_hints ref @
  [hov 0 (str "Expands to: " ++ pr_located_qualid k)])
  | Abbreviation kn ->
    let () = match Abbreviation.search_abbreviation kn with
    | [],Notation_term.NRef (ref,_) -> Dumpglob.add_glob ?loc ref
    | _ -> () in
      v 0 (
      print_abbreviation env kn ++ fnl () ++
      hov 0 (str "Expands to: " ++ pr_located_qualid k))
  | Dir _ | Module _ | ModuleType _ | Undefined _ ->
      hov 0 (pr_located_qualid k)
  | Other (obj, info) -> hov 0 (info.about obj)

let print_about env sigma na udecl =
  match na with
  | {loc;v=Constrexpr.ByNotation (ntn,sc)} ->
      print_about_any ?loc env sigma
        (Term (Notation.interp_notation_as_global_reference ?loc ~head:false (fun _ -> true)
               ntn sc)) udecl
  | {loc;v=Constrexpr.AN ref} ->
      print_about_any ?loc env sigma (locate_any_name ref) udecl

(* for debug *)
let inspect env sigma depth =
  print_context env sigma false (Some depth) (Lib.contents ())

(*************************************************************************)
(* Pretty-printing functions coming from classops.ml                     *)

open Coercionops

let print_coercion_value v = Printer.pr_global v.coe_value

let print_path ((i,j),p) =
  hov 2 (
    str"[" ++ hov 0 (prlist_with_sep pr_semicolon print_coercion_value p) ++
    str"] : ") ++
  pr_class i ++ str" >-> " ++ pr_class j ++
  str (if path_is_reversible p then " (reversible)" else "")

let _ = Coercionops.install_path_printer print_path

let print_graph () =
  prlist_with_sep fnl print_path (inheritance_graph())

let print_classes () =
  pr_sequence pr_class (classes())

let print_coercions () =
  pr_sequence print_coercion_value (coercions())

let print_path_between cls clt =
  let p =
    try
      lookup_path_between_class (cls, clt)
    with Not_found ->
      user_err
        (str"No path between " ++ pr_class cls ++ str" and " ++ pr_class clt
         ++ str ".")
  in
  print_path ((cls, clt), p)

let print_canonical_projections env sigma grefs =
  let open Structures in
  let match_proj_gref { CSTable.projection; value; solution } gr =
    GlobRef.equal projection gr ||
    begin match value with
      | ValuePattern.Const_cs y -> GlobRef.equal y gr
      | _ -> false
    end ||
    GlobRef.equal solution gr
  in
  let projs =
    List.filter (fun p -> List.for_all (match_proj_gref p) grefs)
      (CSTable.entries ())
  in
  prlist_with_sep fnl
    (fun { CSTable.projection; value; solution } ->
    ValuePattern.print value ++
    str " <- " ++
    pr_global projection ++ str " ( " ++ pr_global solution ++ str " )")
    projs

(*************************************************************************)

(*************************************************************************)
(* Pretty-printing functions for type classes                     *)

open Typeclasses

let pr_typeclass env t =
  print_ref false t.cl_impl None

let print_typeclasses () =
  let env = Global.env () in
    prlist_with_sep fnl (pr_typeclass env) (typeclasses ())

let pr_instance env i =
  (*   gallina_print_constant_with_infos i.is_impl *)
  (* lighter *)
  print_ref false (instance_impl i) None ++
  begin match hint_priority i with
  | None -> mt ()
  | Some i -> spc () ++ str "|" ++ spc () ++ int i
  end

let print_all_instances () =
  let env = Global.env () in
  let inst = all_instances () in
    prlist_with_sep fnl (pr_instance env) inst

let print_instances r =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let inst = instances env sigma r in
    prlist_with_sep fnl (pr_instance env) inst
