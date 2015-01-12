(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Term
open Pp
open Names
open Environ
open Declarations
open Nameops
open Globnames
open Libnames
open Goptions

(** Note: there is currently two modes for printing modules.
    - The "short" one, that just prints the names of the fields.
    - The "rich" one, that also tries to print the types of the fields.
    The short version used to be the default behavior, but now we print
    types by default. The following option allows changing this.
    Technically, the environments in this file are either None in
    the "short" mode or (Some env) in the "rich" one.
*)

let short = ref false

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "short module printing";
      optkey   = ["Short";"Module";"Printing"];
      optread  = (fun () -> !short) ;
      optwrite = ((:=) short) }

(** Each time we have to print a non-globally visible structure,
    we place its elements in a fake fresh namespace. *)

let mk_fake_top =
  let r = ref 0 in
  fun () -> incr r; Id.of_string ("FAKETOP"^(string_of_int !r))

module Make (Taggers : sig
  val tag_definition : std_ppcmds -> std_ppcmds
  val tag_keyword : std_ppcmds -> std_ppcmds
end) =
struct

let def s = Taggers.tag_definition (str s)
let keyword s = Taggers.tag_keyword (str s)

let get_new_id locals id =
  let rec get_id l id =
    let dir = DirPath.make [id] in
      if not (Nametab.exists_module dir) then
	id
      else
	get_id (id::l) (Namegen.next_ident_away id l)
  in
    get_id (List.map snd locals) id

(** Inductive declarations *)

open Termops
open Reduction

let print_params env sigma params =
  if List.is_empty params then mt ()
  else Printer.pr_rel_context env sigma params ++ brk(1,2)

let print_constructors envpar names types =
  let pc =
    prlist_with_sep (fun () -> brk(1,0) ++ str "| ")
      (fun (id,c) -> pr_id id ++ str " : " ++ Printer.pr_lconstr_env envpar Evd.empty c)
      (Array.to_list (Array.map2 (fun n t -> (n,t)) names types))
  in
  hv 0 (str "  " ++ pc)

let build_ind_type env mip =
  Inductive.type_of_inductive env mip

let print_one_inductive env mib ((_,i) as ind) =
  let u = if mib.mind_polymorphic then 
      Univ.UContext.instance mib.mind_universes 
    else Univ.Instance.empty in
  let mip = mib.mind_packets.(i) in
  let params = Inductive.inductive_paramdecls (mib,u) in
  let args = extended_rel_list 0 params in
  let arity = hnf_prod_applist env (build_ind_type env ((mib,mip),u)) args in
  let cstrtypes = Inductive.type_of_constructors (ind,u) (mib,mip) in
  let cstrtypes = Array.map (fun c -> hnf_prod_applist env c args) cstrtypes in
  let envpar = push_rel_context params env in
  hov 0 (
    pr_id mip.mind_typename ++ brk(1,4) ++ print_params env Evd.empty params ++
    str ": " ++ Printer.pr_lconstr_env envpar Evd.empty arity ++ str " :=") ++
  brk(0,2) ++ print_constructors envpar mip.mind_consnames cstrtypes

let print_mutual_inductive env mind mib =
  let inds = List.init (Array.length mib.mind_packets) (fun x -> (mind, x))
  in
  let keyword =
    let open Decl_kinds in
    match mib.mind_finite with
    | Finite -> "Inductive"
    | BiFinite -> "Variant"
    | CoFinite -> "CoInductive"
  in
  hov 0 (Printer.pr_polymorphic mib.mind_polymorphic ++
    def keyword ++ spc () ++
    prlist_with_sep (fun () -> fnl () ++ str"  with ")
      (print_one_inductive env mib) inds ++
      Printer.pr_universe_ctx (Univ.instantiate_univ_context mib.mind_universes))

let get_fields =
  let rec prodec_rec l subst c =
    match kind_of_term c with
    | Prod (na,t,c) ->
        let id = match na with Name id -> id | Anonymous -> Id.of_string "_" in
        prodec_rec ((id,true,Vars.substl subst t)::l) (mkVar id::subst) c
    | LetIn (na,b,_,c) ->
        let id = match na with Name id -> id | Anonymous -> Id.of_string "_" in
        prodec_rec ((id,false,Vars.substl subst b)::l) (mkVar id::subst) c
    | _               -> List.rev l
  in
  prodec_rec [] []

let print_record env mind mib =
  let u = 
    if mib.mind_polymorphic then 
      Univ.UContext.instance mib.mind_universes 
    else Univ.Instance.empty 
  in
  let mip = mib.mind_packets.(0) in
  let params = Inductive.inductive_paramdecls (mib,u) in
  let args = extended_rel_list 0 params in
  let arity = hnf_prod_applist env (build_ind_type env ((mib,mip),u)) args in
  let cstrtypes = Inductive.type_of_constructors ((mind,0),u) (mib,mip) in
  let cstrtype = hnf_prod_applist env cstrtypes.(0) args in
  let fields = get_fields cstrtype in
  let envpar = push_rel_context params env in
  let keyword =
    let open Decl_kinds in
    match mib.mind_finite with
    | BiFinite -> "Record"
    | Finite -> "Inductive"
    | CoFinite -> "CoInductive"
  in
  hov 0 (
    hov 0 (
      Printer.pr_polymorphic mib.mind_polymorphic ++
      def keyword ++ spc () ++ pr_id mip.mind_typename ++ brk(1,4) ++
      print_params env Evd.empty params ++
      str ": " ++ Printer.pr_lconstr_env envpar Evd.empty arity ++ brk(1,2) ++
      str ":= " ++ pr_id mip.mind_consnames.(0)) ++
    brk(1,2) ++
    hv 2 (str "{ " ++
      prlist_with_sep (fun () -> str ";" ++ brk(2,0))
        (fun (id,b,c) ->
          pr_id id ++ str (if b then " : " else " := ") ++
          Printer.pr_lconstr_env envpar Evd.empty c) fields) ++ str" }" ++
      Printer.pr_universe_ctx (Univ.instantiate_univ_context mib.mind_universes))

let pr_mutual_inductive_body env mind mib =
  if mib.mind_record <> None && not !Flags.raw_print then
    print_record env mind mib
  else
    print_mutual_inductive env mind mib

(** Modpaths *)

let rec print_local_modpath locals = function
  | MPbound mbid -> pr_id (Util.List.assoc_f MBId.equal mbid locals)
  | MPdot(mp,l) ->
      print_local_modpath locals mp ++ str "." ++ pr_lab l
  | MPfile _ -> raise Not_found

let print_modpath locals mp =
  try (* must be with let because streams are lazy! *)
    let qid = Nametab.shortest_qualid_of_module mp in
      pr_qualid qid
  with
    | Not_found -> print_local_modpath locals mp

let print_kn locals kn =
  try
    let qid = Nametab.shortest_qualid_of_modtype kn in
      pr_qualid qid
  with
      Not_found ->
	try
	  print_local_modpath locals kn
	with
	    Not_found -> print_modpath locals kn

let nametab_register_dir mp =
  let id = mk_fake_top () in
  let dir = DirPath.make [id] in
  Nametab.push_dir (Nametab.Until 1) dir (DirModule (dir,(mp,DirPath.empty)))

(** Nota: the [global_reference] we register in the nametab below
    might differ from internal ones, since we cannot recreate here
    the canonical part of constant and inductive names, but only
    the user names. This works nonetheless since we search now
    [Nametab.the_globrevtab] modulo user name. *)

let nametab_register_body mp dir (l,body) =
  let push id ref =
    Nametab.push (Nametab.Until (1+List.length (DirPath.repr dir)))
      (make_path dir id) ref
  in
  match body with
    | SFBmodule _ -> () (* TODO *)
    | SFBmodtype _ -> () (* TODO *)
    | SFBconst _ ->
      push (Label.to_id l) (ConstRef (Constant.make2 mp l))
    | SFBmind mib ->
      let mind = MutInd.make2 mp l in
      Array.iteri
	(fun i mip ->
	  push mip.mind_typename (IndRef (mind,i));
	  Array.iteri (fun j id -> push id (ConstructRef ((mind,i),j+1)))
	    mip.mind_consnames)
	mib.mind_packets

let nametab_register_module_body mp struc =
  (* If [mp] is a globally visible module, we simply import it *)
  try Declaremods.really_import_module mp
  with Not_found ->
    (* Otherwise we try to emulate an import by playing with nametab *)
    nametab_register_dir mp;
    List.iter (nametab_register_body mp DirPath.empty) struc

let get_typ_expr_alg mtb = match mtb.mod_type_alg with
  | Some (NoFunctor me) -> me
  | _ -> raise Not_found

let nametab_register_modparam mbid mtb =
  match mtb.mod_type with
  | MoreFunctor _ -> () (* functorial param : nothing to register *)
  | NoFunctor struc ->
    (* We first try to use the algebraic type expression if any,
       via a Declaremods function that converts back to module entries *)
    try
      Declaremods.process_module_binding mbid (get_typ_expr_alg mtb)
    with e when Errors.noncritical e ->
      (* Otherwise, we try to play with the nametab ourselves *)
      let mp = MPbound mbid in
      let dir = DirPath.make [MBId.to_id mbid] in
      nametab_register_dir mp;
      List.iter (nametab_register_body mp dir) struc

let print_body is_impl env mp (l,body) =
  let name = str (Label.to_string l) in
  hov 2 (match body with
    | SFBmodule _ -> keyword "Module" ++ spc () ++ name
    | SFBmodtype _ -> keyword "Module Type" ++ spc () ++ name
    | SFBconst cb ->
      (match cb.const_body with
	| Def _ -> def "Definition" ++ spc ()
	| OpaqueDef _ when is_impl -> def "Theorem" ++ spc ()
	| _ -> def "Parameter" ++ spc ()) ++ name ++
      (match env with
	  | None -> mt ()
	  | Some env ->
	    str " :" ++ spc () ++
	    hov 0 (Printer.pr_ltype_env env Evd.empty (* No evars in modules *)
		     (Typeops.type_of_constant_type env cb.const_type)) ++
	    (match cb.const_body with
	      | Def l when is_impl ->
		spc () ++
		hov 2 (str ":= " ++
		       Printer.pr_lconstr_env env Evd.empty (Mod_subst.force_constr l))
	      | _ -> mt ()) ++ str "." ++
	    Printer.pr_universe_ctx cb.const_universes)
    | SFBmind mib ->
      try
	let env = Option.get env in
	pr_mutual_inductive_body env (MutInd.make2 mp l) mib
      with e when Errors.noncritical e ->
        let keyword =
          let open Decl_kinds in
          match mib.mind_finite with
          | Finite -> def "Inductive"
          | BiFinite -> def "Variant"
          | CoFinite -> def "CoInductive"
        in
	keyword ++ spc () ++ name)

let print_struct is_impl env mp struc =
  prlist_with_sep spc (print_body is_impl env mp) struc

let print_structure is_type env mp locals struc =
  let env' = Option.map
    (Modops.add_structure mp struc Mod_subst.empty_delta_resolver) env in
  nametab_register_module_body mp struc;
  let kwd = if is_type then "Sig" else "Struct" in
  hv 2 (keyword kwd ++ spc () ++ print_struct false env' mp struc ++
	brk (1,-2) ++ keyword "End")

let rec flatten_app mexpr l = match mexpr with
  | MEapply (mexpr, arg) -> flatten_app mexpr (arg::l)
  | MEident mp -> mp::l
  | MEwith _ -> assert false

let rec print_typ_expr env mp locals mty =
  match mty with
  | MEident kn -> print_kn locals kn
  | MEapply _ ->
      let lapp = flatten_app mty [] in
      let fapp = List.hd lapp in
      let mapp = List.tl lapp in
      hov 3 (str"(" ++ (print_kn locals fapp) ++ spc () ++
		 prlist_with_sep spc (print_modpath locals) mapp ++ str")")
  | MEwith(me,WithDef(idl,c))->
      let env' = None in (* TODO: build a proper environment if env <> None *)
      let s = String.concat "." (List.map Id.to_string idl) in
      hov 2 (print_typ_expr env' mp locals me ++ spc() ++ str "with" ++ spc()
             ++ def "Definition"++ spc() ++ str s ++ spc() ++  str ":="++ spc())
  | MEwith(me,WithMod(idl,mp))->
      let s = String.concat "." (List.map Id.to_string idl) in
      hov 2 (print_typ_expr env mp locals me ++ spc() ++ str "with" ++ spc() ++
             keyword "Module"++ spc() ++ str s ++ spc() ++ str ":="++ spc())

let print_mod_expr env mp locals = function
  | MEident mp -> print_modpath locals mp
  | MEapply _ as me ->
      let lapp = flatten_app me [] in
      hov 3
        (str"(" ++ prlist_with_sep spc (print_modpath locals) lapp ++ str")")
  | MEwith _ -> assert false (* No 'with' syntax for modules *)

let rec print_functor fty fatom is_type env mp locals = function
  |NoFunctor me -> fatom is_type env mp locals me
  |MoreFunctor (mbid,mtb1,me2) ->
      nametab_register_modparam mbid mtb1;
      let mp1 = MPbound mbid in
      let pr_mtb1 = fty env mp1 locals mtb1 in
      let env' = Option.map (Modops.add_module_type mp1 mtb1) env in
      let locals' = (mbid, get_new_id locals (MBId.to_id mbid))::locals in
      let kwd = if is_type then "Funsig" else "Functor" in
      hov 2
        (keyword kwd ++ spc () ++
	 str "(" ++ pr_id (MBId.to_id mbid) ++ str ":" ++ pr_mtb1 ++ str ")" ++
	 spc() ++ print_functor fty fatom is_type env' mp locals' me2)

let rec print_expression x =
  print_functor
    print_modtype
    (function true -> print_typ_expr | false -> print_mod_expr) x

and print_signature x =
  print_functor print_modtype print_structure x

and print_modtype env mp locals mtb = match mtb.mod_type_alg with
  | Some me -> print_expression true env mp locals me
  | None -> print_signature true env mp locals mtb.mod_type

let rec printable_body dir =
  let dir = pop_dirpath dir in
    DirPath.is_empty dir ||
    try
      match Nametab.locate_dir (qualid_of_dirpath dir) with
	  DirOpenModtype _ -> false
	| DirModule _ | DirOpenModule _ -> printable_body dir
	| _ -> true
    with
	Not_found -> true

(** Since we might play with nametab above, we should reset to prior
    state after the printing *)

let print_expression' is_type env mp me =
  States.with_state_protection
    (fun e -> eval_ppcmds (print_expression is_type env mp [] e)) me

let print_signature' is_type env mp me =
  States.with_state_protection
    (fun e -> eval_ppcmds (print_signature is_type env mp [] e)) me

let unsafe_print_module env mp with_body mb =
  let name = print_modpath [] mp in
  let pr_equals = spc () ++ str ":= " in
  let body = match with_body, mb.mod_expr with
    | false, _
    | true, Abstract -> mt()
    | _, Algebraic me -> pr_equals ++ print_expression' false env mp me
    | _, Struct sign -> pr_equals ++ print_signature' false env mp sign
    | _, FullStruct -> pr_equals ++ print_signature' false env mp mb.mod_type
  in
  let modtype = match mb.mod_expr, mb.mod_type_alg with
    | FullStruct, _ -> mt ()
    | _, Some ty -> brk (1,1) ++ str": " ++ print_expression' true env mp ty
    | _, _ -> brk (1,1) ++ str": " ++ print_signature' true env mp mb.mod_type
  in
  hv 0 (keyword "Module" ++ spc () ++ name ++ modtype ++ body)

exception ShortPrinting

let print_module with_body mp =
  let me = Global.lookup_module mp in
  try
    if !short then raise ShortPrinting;
    unsafe_print_module (Some (Global.env ())) mp with_body me ++ fnl ()
  with e when Errors.noncritical e ->
    unsafe_print_module None mp with_body me ++ fnl ()

let print_modtype kn =
  let mtb = Global.lookup_modtype kn in
  let name = print_kn [] kn in
  hv 1
    (keyword "Module Type" ++ spc () ++ name ++ str " =" ++ spc () ++
     (try
	if !short then raise ShortPrinting;
	print_signature' true (Some (Global.env ())) kn mtb.mod_type
      with e when Errors.noncritical e ->
	print_signature' true None kn mtb.mod_type))

end

module Tag =
struct
  let definition =
    let style = Terminal.make ~bold:true ~fg_color:`LIGHT_RED () in
    Ppstyle.make ~style ["module"; "definition"]
  let keyword =
    let style = Terminal.make ~bold:true () in
    Ppstyle.make ~style ["module"; "keyword"]
end

include Make(struct
  let tag t s = Pp.tag (Pp.Tag.inj t Ppstyle.tag) s
  let tag_definition s = tag Tag.definition s
  let tag_keyword s = tag Tag.keyword s
end)
