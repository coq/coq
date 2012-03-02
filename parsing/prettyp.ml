(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Inductive
open Inductiveops
open Sign
open Reduction
open Environ
open Declare
open Impargs
open Libobject
open Printer
open Printmod
open Libnames
open Nametab
open Recordops

type object_pr = {
  print_inductive           : mutual_inductive -> std_ppcmds;
  print_constant_with_infos : constant -> std_ppcmds;
  print_section_variable    : variable -> std_ppcmds;
  print_syntactic_def       : kernel_name -> std_ppcmds;
  print_module              : bool -> Names.module_path -> std_ppcmds;
  print_modtype             : module_path -> std_ppcmds;
  print_named_decl          : identifier * constr option * types -> std_ppcmds;
  print_library_entry       : bool -> (object_name * Lib.node) -> std_ppcmds option;
  print_context             : bool -> int option -> Lib.library_segment -> std_ppcmds;
  print_typed_value_in_env  : Environ.env -> Term.constr * Term.types -> Pp.std_ppcmds;
  print_eval                : Reductionops.reduction_function -> env -> Evd.evar_map -> Topconstr.constr_expr -> unsafe_judgment -> std_ppcmds;
}

let gallina_print_module  = print_module
let gallina_print_modtype = print_modtype

(**************)
(** Utilities *)

let print_closed_sections = ref false

let pr_infos_list l = v 0 (prlist_with_sep cut (fun x -> x) l) ++ fnl()

let with_line_skip l = if l = [] then mt() else fnl() ++ pr_infos_list l

let blankline = mt() (* add a blank sentence in the list of infos *)

let add_colon prefix = if ismt prefix then mt () else prefix ++ str ": "

let int_or_no n = if n=0 then str "no" else int n

(*******************)
(** Basic printing *)

let print_basename sp = pr_global (ConstRef sp)

let print_ref reduce ref =
  let typ = Global.type_of_global ref in
  let typ =
    if reduce then
      let ctx,ccl = Reductionops.splay_prod_assum (Global.env()) Evd.empty typ
      in it_mkProd_or_LetIn ccl ctx
    else typ in
  hov 0 (pr_global ref ++ str " :" ++ spc () ++ pr_ltype typ)

(********************************)
(** Printing implicit arguments *)

let conjugate_verb_to_be = function [_] -> "is" | _ -> "are"

let pr_impl_name imp = pr_id (name_of_implicit imp)

let print_impargs_by_name max = function
  | []  -> []
  | impls ->
     [hov 0 (str (plural (List.length impls) "Argument") ++ spc() ++
      prlist_with_sep pr_comma pr_impl_name impls ++ spc() ++
      str (conjugate_verb_to_be impls) ++ str" implicit" ++
      (if max then strbrk " and maximally inserted" else mt()))]

let print_one_impargs_list l =
  let imps = List.filter is_status_implicit l in
  let maximps = List.filter Impargs.maximal_insertion_of imps in
  let nonmaximps = list_subtract imps maximps in
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
	   (if n1 = n2 then int_or_no n2 else
	    if n1 = 0 then str "less than " ++ int n2
	    else int n1 ++ str " to " ++ int_or_no n2) ++
	    str (plural n2 " argument") ++ str ":";
          v 0 (prlist_with_sep cut (fun x -> x)
	    (if List.exists is_status_implicit imps
	    then print_one_impargs_list imps
	    else [str "No implicit arguments"]))])]) l)

let print_renames_list prefix l =
  if l = [] then [] else
  [add_colon prefix ++ str "Arguments are renamed to " ++
    hv 2 (prlist_with_sep pr_comma (fun x -> x) (List.map pr_name l))]

let need_expansion impl ref =
  let typ = Global.type_of_global ref in
  let ctx = (prod_assum typ) in
  let nprods = List.length (List.filter (fun (_,b,_) -> b=None) ctx) in
  impl <> [] & List.length impl >= nprods &
    let _,lastimpl = list_chop nprods impl in
      List.filter is_status_implicit lastimpl <> []

let print_impargs ref =
  let ref = Smartlocate.smart_global ref in
  let impl = implicits_of_global ref in
  let has_impl = impl <> [] in
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
  | l when not (List.for_all ((=) None) l) ->
     [add_colon prefix ++ hov 2 (str"Argument scopes are" ++ spc() ++
      str "[" ++
      pr_sequence (function Some sc -> str sc | None -> str "_") l ++
      str "]")]
  | _  -> []

(*****************************)
(** Printing simpl behaviour *)

let print_simpl_behaviour ref =
  match Tacred.get_simpl_behaviour ref with
  | None -> []
  | Some (recargs, nargs, flags) ->
     let never = List.mem `SimplNeverUnfold flags in
     let nomatch = List.mem `SimplDontExposeCase flags in
     let pp_nomatch = spc() ++ if nomatch then
       str "avoiding to expose match constructs" else str"" in
     let pp_recargs = spc() ++ str "when the " ++
       pr_enum (fun x -> pr_nth (x+1)) recargs ++ str (plural (List.length recargs) " argument") ++
       str (plural (if List.length recargs >= 2 then 1 else 2) " evaluate") ++
       str " to a constructor" in
     let pp_nargs =
       spc() ++ str "when applied to " ++ int nargs ++
       str (plural nargs " argument") in
     [hov 2 (str "The simpl tactic " ++
     match recargs, nargs, never with
     | _,_, true -> str "never unfolds " ++ pr_global ref
     | [], 0, _ -> str "always unfolds " ++ pr_global ref
     | _::_, n, _ when n < 0 ->
        str "unfolds " ++ pr_global ref ++ pp_recargs ++ pp_nomatch
     | _::_, n, _ when n > List.fold_left max 0 recargs ->
        str "unfolds " ++ pr_global ref ++ pp_recargs ++
        str " and" ++ pp_nargs ++ pp_nomatch
     | _::_, _, _ ->
        str "unfolds " ++ pr_global ref ++ pp_recargs ++ pp_nomatch
     | [], n, _ when n > 0 ->
        str "unfolds " ++ pr_global ref ++ pp_nargs ++ pp_nomatch
     | _ -> str "unfolds " ++ pr_global ref ++ pp_nomatch )]
;;

(*********************)
(** Printing Opacity *)

type opacity =
  | FullyOpaque
  | TransparentMaybeOpacified of Conv_oracle.level

let opacity env = function
  | VarRef v when pi2 (Environ.lookup_named v env) <> None ->
      Some(TransparentMaybeOpacified (Conv_oracle.get_strategy(VarKey v)))
  | ConstRef cst ->
      let cb = Environ.lookup_constant cst env in
      (match cb.const_body with
	| Undef _ -> None
	| OpaqueDef _ -> Some FullyOpaque
	| Def _ -> Some
          (TransparentMaybeOpacified (Conv_oracle.get_strategy(ConstKey cst))))
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
          | TransparentMaybeOpacified lev when lev = Conv_oracle.transparent ->
              "transparent"
          | TransparentMaybeOpacified (Conv_oracle.Level n) ->
              "transparent (with expansion weight "^string_of_int n^")"
          | TransparentMaybeOpacified Conv_oracle.Expand ->
              "transparent (with minimal expansion weight)")]

(*******************)
(* *)

let print_name_infos ref =
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
    implicits_of_global (fun l -> positions_of_implicits l <> [])
    print_impargs_list

let print_inductive_renames =
  print_args_data_of_inductive_ids
    (fun r -> try List.hd (Arguments_renaming.arguments_names r) with _ -> [])
    ((<>) Anonymous)
    print_renames_list

let print_inductive_argument_scopes =
  print_args_data_of_inductive_ids
    Notation.find_arguments_scope ((<>) None) print_argument_scopes

(*********************)
(* "Locate" commands *)

type logical_name =
  | Term of global_reference
  | Dir of global_dir_reference
  | Syntactic of kernel_name
  | ModuleType of qualid * module_path
  | Undefined of qualid

let locate_any_name ref =
  let module N = Nametab in
  let (loc,qid) = qualid_of_reference ref in
  try Term (N.locate qid)
  with Not_found ->
  try Syntactic (N.locate_syndef qid)
  with Not_found ->
  try Dir (N.locate_dir qid)
  with Not_found ->
  try ModuleType (qid, N.locate_modtype qid)
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
  | ModuleType (qid,_) ->
      str "Module Type" ++ spc () ++ pr_path (Nametab.full_name_modtype qid)
  | Undefined qid ->
      pr_qualid qid ++ spc () ++ str "not a defined object."

let print_located_qualid ref =
  let (loc,qid) = qualid_of_reference ref in
  let module N = Nametab in
  let expand = function
    | TrueGlobal ref ->
	Term ref, N.shortest_qualid_of_global Idset.empty ref
    | SynDef kn ->
	Syntactic kn, N.shortest_qualid_of_syndef Idset.empty kn in
  match List.map expand (N.locate_extended_all qid) with
    | [] ->
	let (dir,id) = repr_qualid qid in
	if dir = empty_dirpath then
	  str "No object of basename " ++ pr_id id
	else
	  str "No object of suffix " ++ pr_qualid qid
    | l ->
	prlist_with_sep fnl
	(fun (o,oqid) ->
	  hov 2 (pr_located_qualid o ++
	  (if oqid <> qid then
	    spc() ++ str "(shorter name to refer to it in current context is " ++ pr_qualid oqid ++ str")"
	  else
	    mt ()))) l

(******************************************)
(**** Printing declarations and judgments *)
(****  Gallina layer                  *****)

let gallina_print_typed_value_in_env env (trm,typ) =
  (pr_lconstr_env env trm ++ fnl () ++
     str "     : " ++ pr_ltype_env env typ ++ fnl ())

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
  let s = string_of_id id in
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
  pr_mutual_inductive_body env sp mib ++ fnl () ++
  with_line_skip
    (print_inductive_renames sp mipv @
     print_inductive_implicit_args sp mipv @
     print_inductive_argument_scopes sp mipv)

let print_named_decl id =
  gallina_print_named_decl (Global.lookup_named id) ++ fnl ()

let gallina_print_section_variable id =
  print_named_decl id ++
  with_line_skip (print_name_infos (VarRef id))

let print_body = function
  | Some lc  -> pr_lconstr (Declarations.force lc)
  | None -> (str"<no body>")

let print_typed_body (val_0,typ) =
  (print_body val_0 ++ fnl () ++ str "     : " ++ pr_ltype typ)

let ungeneralized_type_of_constant_type = function
  | PolymorphicArity (ctx,a) -> mkArity (ctx, Type a.poly_level)
  | NonPolymorphicType t -> t

let print_constant with_values sep sp =
  let cb = Global.lookup_constant sp in
  let val_0 = body_of_constant cb in
  let typ = ungeneralized_type_of_constant_type cb.const_type in
  hov 0 (
    match val_0 with
    | None ->
	str"*** [ " ++
	print_basename sp ++ str " : " ++ cut () ++ pr_ltype typ ++
	str" ]"
    | _ ->
	print_basename sp ++ str sep ++ cut () ++
	(if with_values then print_typed_body (val_0,typ) else pr_ltype typ))
  ++ fnl ()

let gallina_print_constant_with_infos sp =
  print_constant true " = " sp ++
  with_line_skip (print_name_infos (ConstRef sp))

let gallina_print_syntactic_def kn =
  let qid = Nametab.shortest_qualid_of_syndef Idset.empty kn
  and (vars,a) = Syntax_def.search_syntactic_definition kn in
  let c = Topconstr.glob_constr_of_aconstr dummy_loc a in
  hov 2
    (hov 4
       (str "Notation " ++ pr_qualid qid ++
        prlist (fun id -> spc () ++ pr_id id) (List.map fst vars) ++ 
        spc () ++ str ":=") ++
     spc () ++ Constrextern.without_symbols pr_glob_constr c) ++ fnl ()

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
    | h::rest when n = None or Option.get n > 0 ->
	(match gallina_print_library_entry with_values h with
	  | None -> prec n rest
	  | Some pp -> prec (Option.map ((+) (-1)) n) rest ++ pp ++ fnl ())
    | _ -> mt ()
  in
  prec

let gallina_print_eval red_fun env evmap _ {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env evmap trm in
  (str "     = " ++ gallina_print_typed_value_in_env env (ntrm,typ))

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

let print_typed_value x = print_typed_value_in_env (Global.env ()) x

let print_judgment env {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env (trm, typ)

let print_safe_judgment env j =
  let trm = Safe_typing.j_val j in
  let typ = Safe_typing.j_type j in
  print_typed_value_in_env env (trm, typ)

(*********************)
(* *)

let print_full_context () =
  print_context true None (Lib.contents_after None)

let print_full_context_typ () =
  print_context false None (Lib.contents_after None)

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
		str "Proof " ++ pr_lconstr (Declarations.force_opaque lc)
	      | Def c ->
		str "Definition " ++ print_basename con ++ cut () ++
		str "  : " ++ pr_ltype typ ++ cut () ++ str " := " ++
		pr_lconstr (Declarations.force c))
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
  prec (Lib.contents_after None)

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
        if dir = dir' then (hd::in_cxt) else get_cxt (hd::in_cxt) rest
    | (_,Lib.ClosedSection _)::rest ->
        error "Cannot print the contents of a closed section."
	(* LEM: Actually, we could if we wanted to. *)
    | [] -> []
    | hd::rest -> get_cxt (hd::in_cxt) rest
  in
  let cxt = (Lib.contents_after None) in
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
  | ModuleType (_,kn) -> print_modtype kn
  | Undefined qid ->
  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
    let dir,str = repr_qualid qid in
    if (repr_dirpath dir) <> [] then raise Not_found;
    let (_,c,typ) = Global.lookup_named str in
    (print_named_decl (str,c,typ))
  with Not_found ->
    errorlabstrm
      "print_name" (pr_qualid qid ++ spc () ++ str "not a defined object.")

let print_name = function
  | Genarg.ByNotation (loc,ntn,sc) ->
      print_any_name
        (Term (Notation.interp_notation_as_global_reference loc (fun _ -> true)
               ntn sc))
  | Genarg.AN ref ->
      print_any_name (locate_any_name ref)

let print_opaque_name qid =
  let env = Global.env () in
  match global qid with
    | ConstRef cst ->
	let cb = Global.lookup_constant cst in
        if constant_has_body cb then
	  print_constant_with_infos cst
        else
	  error "Not a defined constant."
    | IndRef (sp,_) ->
        print_inductive sp
    | ConstructRef cstr ->
	let ty = Inductiveops.type_of_constructor env cstr in
	print_typed_value (mkConstruct cstr, ty)
    | VarRef id ->
        let (_,c,ty) = lookup_named id env in
	print_named_decl (id,c,ty)

let print_about_any k =
  match k with
  | Term ref ->
      pr_infos_list
       ([print_ref false ref; blankline] @
	print_name_infos ref @
	print_simpl_behaviour ref @
	print_opacity ref @
	[hov 0 (str "Expands to: " ++ pr_located_qualid k)])
  | Syntactic kn ->
      v 0 (
      print_syntactic_def kn ++
      hov 0 (str "Expands to: " ++ pr_located_qualid k)) ++ fnl()
  | Dir _ | ModuleType _ | Undefined _ ->
      hov 0 (pr_located_qualid k) ++ fnl()

let print_about = function
  | Genarg.ByNotation (loc,ntn,sc) ->
      print_about_any
        (Term (Notation.interp_notation_as_global_reference loc (fun _ -> true)
               ntn sc))
  | Genarg.AN ref ->
      print_about_any (locate_any_name ref)

(* for debug *)
let inspect depth =
  print_context false (Some depth) (Lib.contents_after None)


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
  with _ ->
    errorlabstrm "index_of_class"
      (pr_class cl ++ spc() ++ str "not a defined class.")

let print_path_between cls clt =
  let i = index_of_class cls in
  let j = index_of_class clt in
  let p =
    try
      lookup_path_between_class (i,j)
    with _ ->
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
  print_ref false t.cl_impl ++ fnl ()

let print_typeclasses () =
  let env = Global.env () in
    prlist_with_sep fnl (pr_typeclass env) (typeclasses ())

let pr_instance env i =
  (*   gallina_print_constant_with_infos i.is_impl *)
  (* lighter *)
  print_ref false (instance_impl i) ++ fnl ()

let print_all_instances () =
  let env = Global.env () in
  let inst = all_instances () in
    prlist_with_sep fnl (pr_instance env) inst

let print_instances r =
  let env = Global.env () in
  let inst = instances r in
    prlist_with_sep fnl (pr_instance env) inst

