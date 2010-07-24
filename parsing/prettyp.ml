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
  print_leaf_entry          : bool -> Libnames.object_name * Libobject.obj -> Pp.std_ppcmds;
  print_library_entry       : bool -> (object_name * Lib.node) -> std_ppcmds option;
  print_context             : bool -> int option -> Lib.library_segment -> std_ppcmds;
  print_typed_value_in_env  : Environ.env -> Term.constr * Term.types -> Pp.std_ppcmds;
  print_eval                : Reductionops.reduction_function -> env -> Evd.evar_map -> Topconstr.constr_expr -> unsafe_judgment -> std_ppcmds;
}

let gallina_print_module  = print_module
let gallina_print_modtype = print_modtype

(*********************)
(** Basic printing   *)

let print_basename sp = pr_global (ConstRef sp)

let print_closed_sections = ref false

let with_line_skip p = if ismt p then mt() else (fnl () ++ p)

(********************************)
(** Printing implicit arguments *)

let conjugate_to_be = function [_] -> "is" | _ -> "are"

let pr_implicit imp = pr_id (name_of_implicit imp)

let print_impl_args_by_name max = function
  | []  -> mt ()
  | impls ->
      hov 0 (str (plural (List.length impls) "Argument") ++ spc() ++
      prlist_with_sep pr_comma pr_implicit impls ++ spc() ++
      str (conjugate_to_be impls) ++ str" implicit" ++
      (if max then strbrk " and maximally inserted" else mt())) ++ fnl()

let print_impl_args l =
  let imps = List.filter is_status_implicit l in
  let maximps = List.filter Impargs.maximal_insertion_of imps in
  let nonmaximps = list_subtract imps maximps in
  print_impl_args_by_name false nonmaximps ++
  print_impl_args_by_name true maximps

(*********************)
(** Printing Scopes  *)

let print_ref reduce ref =
  let typ = Global.type_of_global ref in
  let typ =
    if reduce then
      let ctx,ccl = Reductionops.splay_prod_assum (Global.env()) Evd.empty typ
      in it_mkProd_or_LetIn ccl ctx
    else typ in
  hov 0 (pr_global ref ++ str " :" ++ spc () ++ pr_ltype typ) ++ fnl ()

let print_argument_scopes = function
  | [Some sc] -> str"Argument scope is [" ++ str sc ++ str"]" ++ fnl()
  | l when not (List.for_all ((=) None) l) ->
      hov 2 (str"Argument scopes are" ++ spc() ++
      str "[" ++
      prlist_with_sep spc (function Some sc -> str sc | None -> str "_") l ++
      str "]") ++ fnl()
  | _  -> mt()

let need_expansion impl ref =
  let typ = Global.type_of_global ref in
  let ctx = (prod_assum typ) in
  let nprods = List.length (List.filter (fun (_,b,_) -> b=None) ctx) in
  impl <> [] & List.length impl >= nprods &
    let _,lastimpl = list_chop nprods impl in
      List.filter is_status_implicit lastimpl <> []

type opacity =
  | FullyOpaque
  | TransparentMaybeOpacified of Conv_oracle.level

let opacity env = function
  | VarRef v when pi2 (Environ.lookup_named v env) <> None ->
      Some(TransparentMaybeOpacified (Conv_oracle.get_strategy(VarKey v)))
  | ConstRef cst ->
      let cb = Environ.lookup_constant cst env in
      if cb.const_body = None then None
      else if cb.const_opaque then Some FullyOpaque
      else Some
        (TransparentMaybeOpacified (Conv_oracle.get_strategy(ConstKey cst)))
  | _ -> None

let print_opacity ref =
  match opacity (Global.env()) ref with
    | None -> mt ()
    | Some s -> pr_global ref ++ str " is " ++
        str (match s with
          | FullyOpaque -> "opaque"
          | TransparentMaybeOpacified Conv_oracle.Opaque ->
              "basically transparent but considered opaque for reduction"
          | TransparentMaybeOpacified lev when lev = Conv_oracle.transparent ->
              "transparent"
          | TransparentMaybeOpacified (Conv_oracle.Level n) ->
              "transparent (with expansion weight "^string_of_int n^")"
          | TransparentMaybeOpacified Conv_oracle.Expand ->
              "transparent (with minimal expansion weight)") ++ fnl()

let print_name_infos ref =
  let impl = implicits_of_global ref in
  let scopes = Notation.find_arguments_scope ref in
  let type_for_implicit =
    if need_expansion impl ref then
      (* Need to reduce since implicits are computed with products flattened *)
      str "Expanded type for implicit arguments" ++ fnl () ++
      print_ref true ref ++ fnl()
    else mt() in
  type_for_implicit ++ print_impl_args impl ++ print_argument_scopes scopes

let print_id_args_data test pr id l =
  if List.exists test l then
    str"For " ++ pr_id id ++ str": " ++ pr l
  else
    mt()

let print_args_data_of_inductive_ids get test pr sp mipv =
  prvecti
    (fun i mip ->
      print_id_args_data test pr mip.mind_typename (get (IndRef (sp,i))) ++
      prvecti
	(fun j idc ->
	  print_id_args_data test pr idc (get (ConstructRef ((sp,i),j+1))))
        mip.mind_consnames)
    mipv

let print_inductive_implicit_args =
  print_args_data_of_inductive_ids
    implicits_of_global is_status_implicit print_impl_args

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

let print_params env params =
  if params = [] then mt () else pr_rel_context env params ++ brk(1,2)

let print_constructors envpar names types =
  let pc =
    prlist_with_sep (fun () -> brk(1,0) ++ str "| ")
      (fun (id,c) -> pr_id id ++ str " : " ++ pr_lconstr_env envpar c)
      (Array.to_list (array_map2 (fun n t -> (n,t)) names types))
  in
  hv 0 (str "  " ++ pc)

let build_inductive sp tyi =
  let (mib,mip) = Global.lookup_inductive (sp,tyi) in
  let params = mib.mind_params_ctxt in
  let args = extended_rel_list 0 params in
  let env = Global.env() in
  let fullarity = match mip.mind_arity with
    | Monomorphic ar -> ar.mind_user_arity
    | Polymorphic ar ->
	it_mkProd_or_LetIn (mkSort (Type ar.poly_level)) mip.mind_arity_ctxt in
  let arity = hnf_prod_applist env fullarity args in
  let cstrtypes = type_of_constructors env (sp,tyi) in
  let cstrtypes =
    Array.map (fun c -> hnf_prod_applist env c args) cstrtypes in
  let cstrnames = mip.mind_consnames in
  (IndRef (sp,tyi), params, arity, cstrnames, cstrtypes)

let print_one_inductive (sp,tyi) =
  let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp tyi in
  let env = Global.env () in
  let envpar = push_rel_context params env in
  hov 0 (
    pr_global (IndRef (sp,tyi)) ++ brk(1,4) ++ print_params env params ++
    str ": " ++ pr_lconstr_env envpar arity ++ str " :=") ++
  brk(0,2) ++ print_constructors envpar cstrnames cstrtypes

let pr_mutual_inductive finite indl =
  hov 0 (
    str (if finite then "Inductive " else "CoInductive ") ++
    prlist_with_sep (fun () -> fnl () ++ str"  with ")
      print_one_inductive indl)

let get_fields =
  let rec prodec_rec l subst c =
    match kind_of_term c with
    | Prod (na,t,c) ->
	let id = match na with Name id -> id | Anonymous -> id_of_string "_" in
	prodec_rec ((id,true,substl subst t)::l) (mkVar id::subst) c
    | LetIn (na,b,_,c) ->
	let id = match na with Name id -> id | Anonymous -> id_of_string "_" in
	prodec_rec ((id,false,substl subst b)::l) (mkVar id::subst) c
    | _               -> List.rev l
  in
  prodec_rec [] []

let pr_record (sp,tyi) =
  let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp tyi in
  let env = Global.env () in
  let envpar = push_rel_context params env in
  let fields = get_fields cstrtypes.(0) in
  hov 0 (
    hov 0 (
      str "Record " ++ pr_global (IndRef (sp,tyi)) ++ brk(1,4) ++
      print_params env params ++
      str ": " ++ pr_lconstr_env envpar arity ++ brk(1,2) ++
      str ":= " ++ pr_id cstrnames.(0)) ++
    brk(1,2) ++
    hv 2 (str "{ " ++
      prlist_with_sep (fun () -> str ";" ++ brk(2,0))
        (fun (id,b,c) ->
	  pr_id id ++ str (if b then " : " else " := ") ++
	  pr_lconstr_env envpar c) fields) ++ str" }")

let gallina_print_inductive sp =
  let (mib,mip) = Global.lookup_inductive (sp,0) in
  let mipv = mib.mind_packets in
  let names = list_tabulate (fun x -> (sp,x)) (Array.length mipv) in
  (if mib.mind_record & not !Flags.raw_print then
    pr_record (List.hd names)
  else
    pr_mutual_inductive mib.mind_finite names) ++ fnl () ++
  with_line_skip
    (print_inductive_implicit_args sp mipv ++
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
  let val_0 = cb.const_body in
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
  let sep = " := "
  and qid = Nametab.shortest_qualid_of_syndef Idset.empty kn
  and (vars,a) = Syntax_def.search_syntactic_definition kn in
  let c = Topconstr.rawconstr_of_aconstr dummy_loc a in
  str "Notation " ++ pr_qualid qid ++
  prlist_with_sep spc pr_id (List.map fst vars) ++ str sep ++
  Constrextern.without_symbols pr_lrawconstr c ++ fnl ()

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
    | (oname,Lib.OpenedModtype _) ->
	Some (str " >>>>>>> Module Type " ++ pr_name oname)
    | (oname,Lib.ClosedModtype _) ->
        Some (str " >>>>>>> Closed Module Type " ++ pr_name oname)
    | (_,Lib.FrozenState _) ->
	None

let gallina_print_leaf_entry with_values c =
  match gallina_print_leaf_entry with_values c with
    | None    -> mt ()
    | Some pp -> pp ++ fnl()

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
  print_leaf_entry          = gallina_print_leaf_entry;
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
let print_leaf_entry x = !object_pr.print_leaf_entry x
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
	  let con = Global.constant_of_delta (constant_of_kn kn) in
	  let cb = Global.lookup_constant con in
	  let val_0 = cb.const_body in
	  let typ = ungeneralized_type_of_constant_type cb.const_type in
	  hov 0 (
	    match val_0 with
	    | None ->
		str (if cb.const_opaque then "Axiom " else "Parameter ") ++
		print_basename con ++ str " : " ++ cut () ++ pr_ltype typ
	    | Some v ->
		if cb.const_opaque then
		  str "Theorem " ++ print_basename con ++ cut () ++
		  str " : " ++ pr_ltype typ ++ str "." ++ fnl () ++
		  str "Proof " ++ print_body val_0
		else
		  str "Definition " ++ print_basename con ++ cut () ++
		  str "  : " ++ pr_ltype typ ++ cut () ++ str " := " ++
		  print_body val_0) ++ str "." ++ fnl () ++ fnl ()
      | "INDUCTIVE" ->
	  let mind = Global.mind_of_delta (mind_of_kn kn) in
	  let (mib,mip) = Global.lookup_inductive (mind,0) in
	  let mipv = mib.mind_packets in
	  let names = list_tabulate (fun x -> (mind,x)) (Array.length mipv) in
	  pr_mutual_inductive mib.mind_finite names ++ str "." ++
	  fnl () ++ fnl ()
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

let list_filter_vec f vec =
  let rec frec n lf =
    if n < 0 then lf
    else if f vec.(n) then
      frec (n-1) (vec.(n)::lf)
    else
      frec (n-1) lf
  in
  frec (Array.length vec -1) []

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
        if cb.const_body <> None then
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
  begin match k with
  | Term ref ->
      print_ref false ref ++ fnl () ++ print_name_infos ref ++
      print_opacity ref
  | Syntactic kn ->
      print_syntactic_def kn
  | Dir _ | ModuleType _ | Undefined _ ->
      mt () end
  ++
  hov 0 (str "Expands to: " ++ pr_located_qualid k)

let print_about = function
  | Genarg.ByNotation (loc,ntn,sc) ->
      print_about_any
        (Term (Notation.interp_notation_as_global_reference loc (fun _ -> true)
               ntn sc))
  | Genarg.AN ref ->
      print_about_any (locate_any_name ref)

let print_impargs ref =
  let ref = Smartlocate.smart_global ref in
  let impl = implicits_of_global ref in
  let has_impl = List.filter is_status_implicit impl <> [] in
  (* Need to reduce since implicits are computed with products flattened *)
  print_ref (need_expansion impl ref) ref ++ fnl() ++
  (if has_impl then print_impl_args impl
   else (str "No implicit arguments" ++ fnl ()))

let unfold_head_fconst =
  let rec unfrec k = match kind_of_term k with
    | Const cst -> constant_value (Global.env ()) cst
    | Lambda (na,t,b) -> mkLambda (na,t,unfrec b)
    | App (f,v) -> appvect (unfrec f,v)
    | _ -> k
  in
  unfrec

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
  prlist_with_sep pr_fnl print_path (inheritance_graph())

let print_classes () =
  prlist_with_sep pr_spc pr_class (classes())

let print_coercions () =
  prlist_with_sep pr_spc print_coercion_value (coercions())

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
  prlist_with_sep pr_fnl
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
  print_ref false (instance_impl i)

let print_all_instances () =
  let env = Global.env () in
  let inst = all_instances () in
    prlist_with_sep fnl (pr_instance env) inst

let print_instances r =
  let env = Global.env () in
  let inst = instances r in
    prlist_with_sep fnl (pr_instance env) inst

