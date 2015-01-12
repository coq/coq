(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Changed by (and thus parts copyright ©) by Lionel Elie Mamane <lionel@mamane.lu>
 * on May-June 2006 for implementation of abstraction of pretty-printing of objects.
 *)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Environ
open Impargs
open Libobject
open Libnames
open Globnames
open Recordops
open Misctypes
open Printer
open Printmod

type object_pr = {
  print_inductive           : mutual_inductive -> std_ppcmds;
  print_constant_with_infos : constant -> std_ppcmds;
  print_section_variable    : variable -> std_ppcmds;
  print_syntactic_def       : kernel_name -> std_ppcmds;
  print_module              : bool -> Names.module_path -> std_ppcmds;
  print_modtype             : module_path -> std_ppcmds;
  print_named_decl          : Id.t * constr option * types -> std_ppcmds;
  print_library_entry       : bool -> (object_name * Lib.node) -> std_ppcmds option;
  print_context             : bool -> int option -> Lib.library_segment -> std_ppcmds;
  print_typed_value_in_env  : Environ.env -> Evd.evar_map -> Term.constr * Term.types -> Pp.std_ppcmds;
  print_eval                : Reductionops.reduction_function -> env -> Evd.evar_map -> Constrexpr.constr_expr -> unsafe_judgment -> std_ppcmds;
}

let gallina_print_module  = print_module
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

let print_basename sp = pr_global (ConstRef sp)

let print_ref reduce ref =
  let typ = Global.type_of_global_unsafe ref in
  let typ =
    if reduce then
      let ctx,ccl = Reductionops.splay_prod_assum (Global.env()) Evd.empty typ
      in it_mkProd_or_LetIn ccl ctx
    else typ in
  let univs = Global.universes_of_global ref in
  hov 0 (pr_global ref ++ str " :" ++ spc () ++ pr_ltype typ ++ 
  	   Printer.pr_universe_ctx univs)

(********************************)
(** Printing implicit arguments *)

let pr_impl_name imp = pr_id (name_of_implicit imp)

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
  let nonmaximps = List.subtract Pervasives.(=) imps maximps in (* FIXME *)
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
	    if Int.equal n1 0 then str "less than " ++ int n2
	    else int n1 ++ str " to " ++ int_or_no n2) ++
	    str (String.plural n2 " argument") ++ str ":";
          v 0 (prlist_with_sep cut (fun x -> x)
	    (if List.exists is_status_implicit imps
	    then print_one_impargs_list imps
	    else [str "No implicit arguments"]))])]) l)

let print_renames_list prefix l =
  if List.is_empty l then [] else
  [add_colon prefix ++ str "Arguments are renamed to " ++
    hv 2 (prlist_with_sep pr_comma (fun x -> x) (List.map pr_name l))]

let need_expansion impl ref =
  let typ = Global.type_of_global_unsafe ref in
  let ctx = prod_assum typ in
  let nprods = List.length (List.filter (fun (_,b,_) -> Option.is_empty b) ctx) in
  not (List.is_empty impl) && List.length impl >= nprods &&
    let _,lastimpl = List.chop nprods impl in
      List.exists is_status_implicit lastimpl

let print_impargs ref =
  let ref = Smartlocate.smart_global ref in
  let impl = implicits_of_global ref in
  let has_impl = not (List.is_empty impl) in
  (* Need to reduce since implicits are computed with products flattened *)
  pr_infos_list
    ([ print_ref (need_expansion (select_impargs_size 0 impl) ref) ref;
       blankline ] @
    (if has_impl then print_impargs_list (mt()) impl
     else [str "No implicit arguments"]))

(*********************)
(** Printing Scopes  *)

let print_argument_scopes prefix = function
  | [Some sc] ->
      [add_colon prefix ++ str"Argument scope is [" ++ str sc ++ str"]"]
  | l when not (List.for_all Option.is_empty l) ->
     [add_colon prefix ++ hov 2 (str"Argument scopes are" ++ spc() ++
      str "[" ++
      pr_sequence (function Some sc -> str sc | None -> str "_") l ++
      str "]")]
  | _  -> []

(*********************)
(** Printing Opacity *)

type opacity =
  | FullyOpaque
  | TransparentMaybeOpacified of Conv_oracle.level

let opacity env = function
  | VarRef v when not (Option.is_empty (pi2 (Environ.lookup_named v env))) ->
      Some(TransparentMaybeOpacified
        (Conv_oracle.get_strategy (Environ.oracle env) (VarKey v)))
  | ConstRef cst ->
      let cb = Environ.lookup_constant cst env in
      (match cb.const_body with
	| Undef _ -> None
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
        str (match s with
          | FullyOpaque -> "opaque"
          | TransparentMaybeOpacified Conv_oracle.Opaque ->
              "basically transparent but considered opaque for reduction"
          | TransparentMaybeOpacified lev when Conv_oracle.is_transparent lev ->
              "transparent"
          | TransparentMaybeOpacified (Conv_oracle.Level n) ->
              "transparent (with expansion weight "^string_of_int n^")"
          | TransparentMaybeOpacified Conv_oracle.Expand ->
              "transparent (with minimal expansion weight)")]

(*******************)
(* *)

let print_polymorphism ref =
  let poly = Global.is_polymorphic ref in
  let template_poly = Global.is_template_polymorphic ref in
    pr_global ref ++ str " is " ++ str 
      (if poly then "universe polymorphic"
       else if template_poly then
	 "template universe polymorphic"
       else "not universe polymorphic")

let print_primitive_record mipv = function
  | Some (Some (_, ps,_)) ->
    [pr_id mipv.(0).mind_typename ++ str" is primitive and has eta conversion."]
  | _ -> []
    
let print_primitive ref =
  match ref with 
  | IndRef ind -> 
    let mib,_ = Global.lookup_inductive ind in
      print_primitive_record mib.mind_packets mib.mind_record
  | _ -> []
    
let print_name_infos ref =
  let poly = print_polymorphism ref in
  let impls = implicits_of_global ref in
  let scopes = Notation.find_arguments_scope ref in
  let renames =
    try List.hd (Arguments_renaming.arguments_names ref) with Not_found -> [] in
  let type_info_for_implicit =
    if need_expansion (select_impargs_size 0 impls) ref then
      (* Need to reduce since implicits are computed with products flattened *)
      [str "Expanded type for implicit arguments";
       print_ref true ref; blankline]
    else
      [] in
  poly :: print_primitive ref @
  type_info_for_implicit @
  print_renames_list (mt()) renames @
  print_impargs_list (mt()) impls @
  print_argument_scopes (mt()) scopes

let print_id_args_data test pr id l =
  if List.exists test l then
    pr (str "For " ++ pr_id id) l
  else
    []

let print_args_data_of_inductive_ids get test pr sp mipv =
  List.flatten (Array.to_list (Array.mapi
    (fun i mip ->
      print_id_args_data test pr mip.mind_typename (get (IndRef (sp,i))) @
      List.flatten (Array.to_list (Array.mapi
	(fun j idc ->
	  print_id_args_data test pr idc (get (ConstructRef ((sp,i),j+1))))
        mip.mind_consnames)))
    mipv))

let print_inductive_implicit_args =
  print_args_data_of_inductive_ids
    implicits_of_global (fun l -> not (List.is_empty (positions_of_implicits l)))
    print_impargs_list

let print_inductive_renames =
  print_args_data_of_inductive_ids
    (fun r ->
      try List.hd (Arguments_renaming.arguments_names r) with Not_found -> [])
    ((!=) Anonymous)
    print_renames_list

let print_inductive_argument_scopes =
  print_args_data_of_inductive_ids
    Notation.find_arguments_scope (Option.has_some) print_argument_scopes

(*********************)
(* "Locate" commands *)

type logical_name =
  | Term of global_reference
  | Dir of global_dir_reference
  | Syntactic of kernel_name
  | ModuleType of module_path
  | Tactic of Nametab.ltac_constant
  | Undefined of qualid

let locate_any_name ref =
  let (loc,qid) = qualid_of_reference ref in
  try Term (Nametab.locate qid)
  with Not_found ->
  try Syntactic (Nametab.locate_syndef qid)
  with Not_found ->
  try Dir (Nametab.locate_dir qid)
  with Not_found ->
  try ModuleType (Nametab.locate_modtype qid)
  with Not_found -> Undefined qid

let pr_located_qualid = function
  | Term ref ->
      let ref_str = match ref with
	  ConstRef _ -> "Constant"
	| IndRef _ -> "Inductive"
	| ConstructRef _ -> "Constructor"
	| VarRef _ -> "Variable" in
      str ref_str ++ spc () ++ pr_path (Nametab.path_of_global ref)
  | Syntactic kn ->
      str "Notation" ++ spc () ++ pr_path (Nametab.path_of_syndef kn)
  | Dir dir ->
      let s,dir = match dir with
	| DirOpenModule (dir,_) -> "Open Module", dir
	| DirOpenModtype (dir,_) -> "Open Module Type", dir
	| DirOpenSection (dir,_) -> "Open Section", dir
	| DirModule (dir,_) -> "Module", dir
	| DirClosedSection dir -> "Closed Section", dir
      in
      str s ++ spc () ++ pr_dirpath dir
  | ModuleType mp ->
      str "Module Type" ++ spc () ++ pr_path (Nametab.path_of_modtype mp)
  | Tactic kn ->
      str "Ltac" ++ spc () ++ pr_path (Nametab.path_of_tactic kn)
  | Undefined qid ->
      pr_qualid qid ++ spc () ++ str "not a defined object."

let canonize_ref = function
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
    | SynDef kn ->
        Syntactic kn, Nametab.shortest_qualid_of_syndef Id.Set.empty kn
  in
  List.map expand (Nametab.locate_extended_all qid)

let locate_tactic qid =
  let all = Nametab.locate_extended_all_tactic qid in
  List.map (fun kn -> (Tactic kn, Nametab.shortest_qualid_of_tactic kn)) all

let locate_module qid =
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = match dir with
  | DirModule (_, (mp, _)) -> Some (Dir dir, Nametab.shortest_qualid_of_module mp)
  | DirOpenModule _ -> Some (Dir dir, qid)
  | _ -> None
  in
  List.map_filter map all

let locate_modtype qid =
  let all = Nametab.locate_extended_all_modtype qid in
  let map mp = ModuleType mp, Nametab.shortest_qualid_of_modtype mp in
  let modtypes = List.map map all in
  (** Don't forget the opened module types: they are not part of the same name tab. *)
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = match dir with
  | DirOpenModtype _ -> Some (Dir dir, qid)
  | _ -> None
  in
  modtypes @ List.map_filter map all

let print_located_qualid name flags ref =
  let (loc,qid) = qualid_of_reference ref in
  let located = [] in
  let located = if List.mem `LTAC flags then locate_tactic qid @ located else located in
  let located = if List.mem `MODTYPE flags then locate_modtype qid @ located else located in
  let located = if List.mem `MODULE flags then locate_module qid @ located else located in
  let located = if List.mem `TERM flags then locate_term qid @ located else located in
  match located with
    | [] ->
	let (dir,id) = repr_qualid qid in
	if DirPath.is_empty dir then
	  str ("No " ^ name ^ " of basename") ++ spc () ++ pr_id id
	else
	  str ("No " ^ name ^ " of suffix") ++ spc () ++ pr_qualid qid
    | l ->
	prlist_with_sep fnl
	(fun (o,oqid) ->
	  hov 2 (pr_located_qualid o ++
	  (if not (qualid_eq oqid qid) then
	    spc() ++ str "(shorter name to refer to it in current context is "
            ++ pr_qualid oqid ++ str")"
	   else mt ()) ++
          display_alias o)) l

let print_located_term ref = print_located_qualid "term" [`TERM] ref
let print_located_tactic ref = print_located_qualid "tactic" [`LTAC] ref
let print_located_module ref = print_located_qualid "module" [`MODULE; `MODTYPE] ref
let print_located_qualid ref = print_located_qualid "object" [`TERM; `LTAC; `MODULE; `MODTYPE] ref

(******************************************)
(**** Printing declarations and judgments *)
(****  Gallina layer                  *****)

let gallina_print_typed_value_in_env env sigma (trm,typ) =
  (pr_lconstr_env env sigma trm ++ fnl () ++
     str "     : " ++ pr_ltype_env env sigma typ)

(* To be improved; the type should be used to provide the types in the
   abstractions. This should be done recursively inside pr_lconstr, so that
   the pretty-print of a proposition (P:(nat->nat)->Prop)(P [u]u)
   synthesizes the type nat of the abstraction on u *)

let print_named_def name body typ =
  let pbody = pr_lconstr body in
  let ptyp = pr_ltype typ in
  let pbody = if isCast body then surround pbody else pbody in
  (str "*** [" ++ str name ++ str " " ++
     hov 0 (str ":=" ++ brk (1,2) ++ pbody ++ spc () ++
	      str ":" ++ brk (1,2) ++ ptyp) ++
	   str "]")

let print_named_assum name typ =
  str "*** [" ++ str name ++ str " : " ++ pr_ltype typ ++ str "]"

let gallina_print_named_decl (id,c,typ) =
  let s = Id.to_string id in
  match c with
    | Some body -> print_named_def s body typ
    | None -> print_named_assum s typ

let assumptions_for_print lna =
  List.fold_right (fun na env -> add_name na env) lna empty_names_context

(*********************)
(* *)

let gallina_print_inductive sp =
  let env = Global.env() in
  let mib = Environ.lookup_mind sp env in
  let mipv = mib.mind_packets in
  pr_mutual_inductive_body env sp mib ++
  with_line_skip
    (print_primitive_record mipv mib.mind_record @
     print_inductive_renames sp mipv @
     print_inductive_implicit_args sp mipv @
     print_inductive_argument_scopes sp mipv)

let print_named_decl id =
  gallina_print_named_decl (Global.lookup_named id) ++ fnl ()

let gallina_print_section_variable id =
  print_named_decl id ++
  with_line_skip (print_name_infos (VarRef id))

let print_body = function
  | Some c  -> pr_lconstr c
  | None -> (str"<no body>")

let print_typed_body (val_0,typ) =
  (print_body val_0 ++ fnl () ++ str "     : " ++ pr_ltype typ)

let ungeneralized_type_of_constant_type t = 
  Typeops.type_of_constant_type (Global.env ()) t

let print_constant with_values sep sp =
  let cb = Global.lookup_constant sp in
  let val_0 = Global.body_of_constant_body cb in
  let typ = Declareops.type_of_constant cb in
  let typ = ungeneralized_type_of_constant_type typ in
  let univs = Univ.instantiate_univ_context 
    (Global.universes_of_constant_body cb)
  in
  hov 0 (pr_polymorphic cb.const_polymorphic ++
    match val_0 with
    | None ->
	str"*** [ " ++
	print_basename sp ++ str " : " ++ cut () ++ pr_ltype typ ++
	str" ]" ++
	Printer.pr_universe_ctx univs
    | _ ->
	print_basename sp ++ str sep ++ cut () ++
	(if with_values then print_typed_body (val_0,typ) else pr_ltype typ)++
        Printer.pr_universe_ctx univs)

let gallina_print_constant_with_infos sp =
  print_constant true " = " sp ++
  with_line_skip (print_name_infos (ConstRef sp))

let gallina_print_syntactic_def kn =
  let qid = Nametab.shortest_qualid_of_syndef Id.Set.empty kn
  and (vars,a) = Syntax_def.search_syntactic_definition kn in
  let c = Notation_ops.glob_constr_of_notation_constr Loc.ghost a in
  hov 2
    (hov 4
       (str "Notation " ++ pr_qualid qid ++
        prlist (fun id -> spc () ++ pr_id id) (List.map fst vars) ++
        spc () ++ str ":=") ++
     spc () ++
     Constrextern.without_specific_symbols
       [Notation.SynDefRule kn] pr_glob_constr c)

let gallina_print_leaf_entry with_values ((sp,kn as oname),lobj) =
  let sep = if with_values then " = " else " : "
  and tag = object_tag lobj in
    match (oname,tag) with
      | (_,"VARIABLE") ->
	  (* Outside sections, VARIABLES still exist but only with universes
             constraints *)
	  (try Some(print_named_decl (basename sp)) with Not_found -> None)
      | (_,"CONSTANT") ->
	  Some (print_constant with_values sep (constant_of_kn kn))
      | (_,"INDUCTIVE") ->
	  Some (gallina_print_inductive (mind_of_kn kn))
      | (_,"MODULE") ->
	  let (mp,_,l) = repr_kn kn in
	    Some (print_module with_values (MPdot (mp,l)))
      | (_,"MODULE TYPE") ->
	  let (mp,_,l) = repr_kn kn in
	  Some (print_modtype (MPdot (mp,l)))
      | (_,("AUTOHINT"|"GRAMMAR"|"SYNTAXCONSTANT"|"PPSYNTAX"|"TOKEN"|"CLASS"|
	    "COERCION"|"REQUIRE"|"END-SECTION"|"STRUCTURE")) -> None
      (* To deal with forgotten cases... *)
      | (_,s) -> None

let gallina_print_library_entry with_values ent =
  let pr_name (sp,_) = pr_id (basename sp) in
  match ent with
    | (oname,Lib.Leaf lobj) ->
	gallina_print_leaf_entry with_values (oname,lobj)
    | (oname,Lib.OpenedSection (dir,_)) ->
        Some (str " >>>>>>> Section " ++ pr_name oname)
    | (oname,Lib.ClosedSection _) ->
        Some (str " >>>>>>> Closed Section " ++ pr_name oname)
    | (_,Lib.CompilingLibrary (dir,_)) ->
	Some (str " >>>>>>> Library " ++ pr_dirpath dir)
    | (oname,Lib.OpenedModule _) ->
	Some (str " >>>>>>> Module " ++ pr_name oname)
    | (oname,Lib.ClosedModule _) ->
        Some (str " >>>>>>> Closed Module " ++ pr_name oname)
    | (_,Lib.FrozenState _) ->
	None

let gallina_print_context with_values =
  let rec prec n = function
    | h::rest when Option.is_empty n || Option.get n > 0 ->
	(match gallina_print_library_entry with_values h with
	  | None -> prec n rest
	  | Some pp -> prec (Option.map ((+) (-1)) n) rest ++ pp ++ fnl ())
    | _ -> mt ()
  in
  prec

let gallina_print_eval red_fun env sigma _ {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env sigma trm in
  (str "     = " ++ gallina_print_typed_value_in_env env sigma (ntrm,typ))

(******************************************)
(**** Printing abstraction layer          *)

let default_object_pr = {
  print_inductive           = gallina_print_inductive;
  print_constant_with_infos = gallina_print_constant_with_infos;
  print_section_variable    = gallina_print_section_variable;
  print_syntactic_def       = gallina_print_syntactic_def;
  print_module              = gallina_print_module;
  print_modtype             = gallina_print_modtype;
  print_named_decl          = gallina_print_named_decl;
  print_library_entry       = gallina_print_library_entry;
  print_context             = gallina_print_context;
  print_typed_value_in_env  = gallina_print_typed_value_in_env;
  print_eval                = gallina_print_eval;
}

let object_pr = ref default_object_pr
let set_object_pr = (:=) object_pr

let print_inductive x = !object_pr.print_inductive x
let print_constant_with_infos c = !object_pr.print_constant_with_infos c
let print_section_variable c = !object_pr.print_section_variable c
let print_syntactic_def x = !object_pr.print_syntactic_def x
let print_module x  = !object_pr.print_module  x
let print_modtype x = !object_pr.print_modtype x
let print_named_decl x = !object_pr.print_named_decl x
let print_library_entry x = !object_pr.print_library_entry x
let print_context x = !object_pr.print_context x
let print_typed_value_in_env x = !object_pr.print_typed_value_in_env x
let print_eval x = !object_pr.print_eval x

(******************************************)
(**** Printing declarations and judgments *)
(****  Abstract layer                 *****)

let print_typed_value x = print_typed_value_in_env (Global.env ()) Evd.empty x

let print_judgment env sigma {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env sigma (trm, typ)

let print_safe_judgment env sigma j =
  let trm = Safe_typing.j_val j in
  let typ = Safe_typing.j_type j in
  print_typed_value_in_env env sigma (trm, typ)

(*********************)
(* *)

let print_full_context () = print_context true None (Lib.contents ())
let print_full_context_typ () = print_context false None (Lib.contents ())

let print_full_pure_context () =
  let rec prec = function
  | ((_,kn),Lib.Leaf lobj)::rest ->
      let pp = match object_tag lobj with
      | "CONSTANT" ->
	  let con = Global.constant_of_delta_kn kn in
	  let cb = Global.lookup_constant con in
	  let typ = ungeneralized_type_of_constant_type cb.const_type in
	  hov 0 (
	    match cb.const_body with
	      | Undef _ ->
		str "Parameter " ++
		print_basename con ++ str " : " ++ cut () ++ pr_ltype typ
	      | OpaqueDef lc ->
		str "Theorem " ++ print_basename con ++ cut () ++
		str " : " ++ pr_ltype typ ++ str "." ++ fnl () ++
		str "Proof " ++ pr_lconstr (Opaqueproof.force_proof (Global.opaque_tables ()) lc)
	      | Def c ->
		str "Definition " ++ print_basename con ++ cut () ++
		str "  : " ++ pr_ltype typ ++ cut () ++ str " := " ++
		pr_lconstr (Mod_subst.force_constr c))
          ++ str "." ++ fnl () ++ fnl ()
      | "INDUCTIVE" ->
	  let mind = Global.mind_of_delta_kn kn in
	  let mib = Global.lookup_mind mind in
	  pr_mutual_inductive_body (Global.env()) mind mib ++
	    str "." ++ fnl () ++ fnl ()
      | "MODULE" ->
	  (* TODO: make it reparsable *)
	  let (mp,_,l) = repr_kn kn in
	  print_module true (MPdot (mp,l)) ++ str "." ++ fnl () ++ fnl ()
      | "MODULE TYPE" ->
	  (* TODO: make it reparsable *)
	  (* TODO: make it reparsable *)
	  let (mp,_,l) = repr_kn kn in
	  print_modtype (MPdot (mp,l)) ++ str "." ++ fnl () ++ fnl ()
      | _ -> mt () in
      prec rest ++ pp
  | _::rest -> prec rest
  | _ -> mt () in
  prec (Lib.contents ())

(* For printing an inductive definition with
   its constructors and elimination,
   assume that the declaration of constructors and eliminations
   follows the definition of the inductive type *)

(* This is designed to print the contents of an opened section *)
let read_sec_context r =
  let loc,qid = qualid_of_reference r in
  let dir =
    try Nametab.locate_section qid
    with Not_found ->
      user_err_loc (loc,"read_sec_context", str "Unknown section.") in
  let rec get_cxt in_cxt = function
    | (_,Lib.OpenedSection ((dir',_),_) as hd)::rest ->
        if DirPath.equal dir dir' then (hd::in_cxt) else get_cxt (hd::in_cxt) rest
    | (_,Lib.ClosedSection _)::rest ->
        error "Cannot print the contents of a closed section."
	(* LEM: Actually, we could if we wanted to. *)
    | [] -> []
    | hd::rest -> get_cxt (hd::in_cxt) rest
  in
  let cxt = Lib.contents () in
  List.rev (get_cxt [] cxt)

let print_sec_context sec =
  print_context true None (read_sec_context sec)

let print_sec_context_typ sec =
  print_context false None (read_sec_context sec)

let print_any_name = function
  | Term (ConstRef sp) -> print_constant_with_infos sp
  | Term (IndRef (sp,_)) -> print_inductive sp
  | Term (ConstructRef ((sp,_),_)) -> print_inductive sp
  | Term (VarRef sp) -> print_section_variable sp
  | Syntactic kn -> print_syntactic_def kn
  | Dir (DirModule(dirpath,(mp,_))) -> print_module (printable_body dirpath) mp
  | Dir _ -> mt ()
  | ModuleType mp -> print_modtype mp
  | Tactic kn -> mt () (** TODO *)
  | Undefined qid ->
  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
    let dir,str = repr_qualid qid in
    if not (DirPath.is_empty dir) then raise Not_found;
    let (_,c,typ) = Global.lookup_named str in
    (print_named_decl (str,c,typ))
  with Not_found ->
    errorlabstrm
      "print_name" (pr_qualid qid ++ spc () ++ str "not a defined object.")

let print_name = function
  | ByNotation (loc,ntn,sc) ->
      print_any_name
        (Term (Notation.interp_notation_as_global_reference loc (fun _ -> true)
               ntn sc))
  | AN ref ->
      print_any_name (locate_any_name ref)

let print_opaque_name qid =
  let env = Global.env () in
  match Nametab.global qid with
    | ConstRef cst ->
	let cb = Global.lookup_constant cst in
        if Declareops.constant_has_body cb then
	  print_constant_with_infos cst
        else
	  error "Not a defined constant."
    | IndRef (sp,_) ->
        print_inductive sp
    | ConstructRef cstr as gr ->
	let ty = Universes.unsafe_type_of_global gr in
	print_typed_value (mkConstruct cstr, ty)
    | VarRef id ->
        let (_,c,ty) = lookup_named id env in
	print_named_decl (id,c,ty)

let print_about_any loc k =
  match k with
  | Term ref ->
    let rb = Reductionops.ReductionBehaviour.print ref in
    Dumpglob.add_glob loc ref;
      pr_infos_list
       (print_ref false ref :: blankline ::
	print_name_infos ref @
	(if Pp.ismt rb then [] else [rb]) @
	print_opacity ref @
	[hov 0 (str "Expands to: " ++ pr_located_qualid k)])
  | Syntactic kn ->
    let () = match Syntax_def.search_syntactic_definition kn with
    | [],Notation_term.NRef ref -> Dumpglob.add_glob loc ref
    | _ -> () in
      v 0 (
      print_syntactic_def kn ++ fnl () ++
      hov 0 (str "Expands to: " ++ pr_located_qualid k))
  | Dir _ | ModuleType _ | Tactic _ | Undefined _ ->
      hov 0 (pr_located_qualid k)

let print_about = function
  | ByNotation (loc,ntn,sc) ->
      print_about_any loc
        (Term (Notation.interp_notation_as_global_reference loc (fun _ -> true)
               ntn sc))
  | AN ref ->
      print_about_any (loc_of_reference ref) (locate_any_name ref)

(* for debug *)
let inspect depth =
  print_context false (Some depth) (Lib.contents ())


(*************************************************************************)
(* Pretty-printing functions coming from classops.ml                     *)

open Classops

let print_coercion_value v = pr_lconstr (get_coercion_value v)

let print_class i =
  let cl,_ = class_info_from_index i in
  pr_class cl

let print_path ((i,j),p) =
  hov 2 (
    str"[" ++ hov 0 (prlist_with_sep pr_semicolon print_coercion_value p) ++
    str"] : ") ++
  print_class i ++ str" >-> " ++ print_class j

let _ = Classops.install_path_printer print_path

let print_graph () =
  prlist_with_sep fnl print_path (inheritance_graph())

let print_classes () =
  pr_sequence pr_class (classes())

let print_coercions () =
  pr_sequence print_coercion_value (coercions())

let index_of_class cl =
  try
    fst (class_info cl)
  with Not_found ->
    errorlabstrm "index_of_class"
      (pr_class cl ++ spc() ++ str "not a defined class.")

let print_path_between cls clt =
  let i = index_of_class cls in
  let j = index_of_class clt in
  let p =
    try
      lookup_path_between_class (i,j)
    with Not_found ->
      errorlabstrm "index_cl_of_id"
        (str"No path between " ++ pr_class cls ++ str" and " ++ pr_class clt
	 ++ str ".")
  in
  print_path ((i,j),p)

let print_canonical_projections () =
  prlist_with_sep fnl
    (fun ((r1,r2),o) -> pr_cs_pattern r2 ++
    str " <- " ++
    pr_global r1 ++ str " ( " ++ pr_lconstr o.o_DEF ++ str " )")
    (canonical_projections ())

(*************************************************************************)

(*************************************************************************)
(* Pretty-printing functions for type classes                     *)

open Typeclasses

let pr_typeclass env t =
  print_ref false t.cl_impl

let print_typeclasses () =
  let env = Global.env () in
    prlist_with_sep fnl (pr_typeclass env) (typeclasses ())

let pr_instance env i =
  (*   gallina_print_constant_with_infos i.is_impl *)
  (* lighter *)
  print_ref false (instance_impl i) ++
  begin match instance_priority i with
  | None -> mt ()
  | Some i -> spc () ++ str "|" ++ spc () ++ int i
  end

let print_all_instances () =
  let env = Global.env () in
  let inst = all_instances () in
    prlist_with_sep fnl (pr_instance env) inst

let print_instances r =
  let env = Global.env () in
  let inst = instances r in
    prlist_with_sep fnl (pr_instance env) inst
