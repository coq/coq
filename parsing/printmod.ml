(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Declarations
open Nameops
open Libnames
open Goptions

(** Note: there is currently two modes for printing modules.
    - The "short" one, that just prints the names of the fields.
    - The "rich" one, that also tries to print the types of the fields.
    The short version used to be the default behavior, but now we print
    types by default. The following option allows to change this.
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

let get_new_id locals id =
  let rec get_id l id =
    let dir = make_dirpath [id] in
      if not (Nametab.exists_module dir) then
	id
      else
	get_id (id::l) (Namegen.next_ident_away id l)
  in
    get_id (List.map snd locals) id

let rec print_local_modpath locals = function
  | MPbound mbid -> pr_id (List.assoc mbid locals)
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
  let id = id_of_string "FAKETOP" in
  let fp = Libnames.make_path empty_dirpath id in
  let dir = make_dirpath [id] in
  Nametab.push_dir (Nametab.Until 1) dir (DirModule (dir,(mp,empty_dirpath)));
  fp

(** Nota: the [global_reference] we register in the nametab below
    might differ from internal ones, since we cannot recreate here
    the canonical part of constant and inductive names, but only
    the user names. This works nonetheless since we search now
    [Nametab.the_globrevtab] modulo user name. *)

let nametab_register_body mp fp (l,body) =
  let push id ref =
    Nametab.push (Nametab.Until 1) (make_path (dirpath fp) id) ref
  in
  match body with
    | SFBmodule _ -> () (* TODO *)
    | SFBmodtype _ -> () (* TODO *)
    | SFBconst _ ->
      push (id_of_label l) (ConstRef (make_con mp empty_dirpath l))
    | SFBmind mib ->
      let mind = make_mind mp empty_dirpath l in
      Array.iteri
	(fun i mip ->
	  push mip.mind_typename (IndRef (mind,i));
	  Array.iteri (fun j id -> push id (ConstructRef ((mind,i),j+1)))
	    mip.mind_consnames)
	mib.mind_packets

let print_body is_impl env mp (l,body) =
  let name = str (string_of_label l) in
  hov 2 (match body with
    | SFBmodule _ -> str "Module " ++ name
    | SFBmodtype _ -> str "Module Type " ++ name
    | SFBconst cb ->
      (match cb.const_body with
	| Def _ -> str "Definition "
	| OpaqueDef _ when is_impl -> str "Theorem "
	| _ -> str "Parameter ") ++ name ++
      (match env with
	  | None -> mt ()
	  | Some env ->
	    str " :" ++ spc () ++
	    hov 0 (Printer.pr_ltype_env env
		     (Typeops.type_of_constant_type env cb.const_type)) ++
	    (match cb.const_body with
	      | Def l when is_impl ->
		spc () ++
		hov 2 (str ":= " ++
		       Printer.pr_lconstr_env env (Declarations.force l))
	      | _ -> mt ()) ++
            str ".")
    | SFBmind mib ->
      try
	let env = Option.get env in
	Printer.pr_mutual_inductive_body env (make_mind mp empty_dirpath l) mib
      with _ ->
	(if mib.mind_finite then str "Inductive " else str "CoInductive")
	++ name)

let print_struct is_impl env mp struc =
  begin
    (* If [mp] is a globally visible module, we simply import it *)
    try Declaremods.really_import_module mp
    with _ ->
    (* Otherwise we try to emulate an import by playing with nametab *)
      let fp = nametab_register_dir mp in
      List.iter (nametab_register_body mp fp) struc
  end;
  prlist_with_sep spc (print_body is_impl env mp) struc

let rec flatten_app mexpr l = match mexpr with
  | SEBapply (mexpr, SEBident arg,_) -> flatten_app mexpr (arg::l)
  | SEBident mp -> mp::l
  | _ -> assert false

let rec print_modtype env mp locals mty =
  match mty with
    | SEBident kn -> print_kn locals kn
    | SEBfunctor (mbid,mtb1,mtb2) ->
      let mp1 = MPbound mbid in
      let env' = Option.map
	  (Modops.add_module (Modops.module_body_of_type mp1 mtb1)) env in
      let seb1 = Option.default mtb1.typ_expr mtb1.typ_expr_alg in
      let locals' = (mbid, get_new_id locals (id_of_mbid mbid))::locals
      in
      (try Declaremods.process_module_seb_binding mbid seb1 with _ -> ());
      hov 2 (str "Funsig" ++ spc () ++ str "(" ++
	       pr_id (id_of_mbid mbid) ++ str ":" ++
	       print_modtype env mp1 locals seb1 ++
	       str ")" ++ spc() ++ print_modtype env' mp locals' mtb2)
  | SEBstruct (sign) ->
      let env' = Option.map
	(Modops.add_signature mp sign Mod_subst.empty_delta_resolver) env in
      hv 2 (str "Sig" ++ spc () ++ print_struct false env' mp sign ++
	    brk (1,-2) ++ str "End")
  | SEBapply _ ->
      let lapp = flatten_app mty [] in
      let fapp = List.hd lapp in
      let mapp = List.tl lapp in
      hov 3 (str"(" ++ (print_kn locals fapp) ++ spc () ++
		 prlist_with_sep spc (print_modpath locals) mapp ++ str")")
  | SEBwith(seb,With_definition_body(idl,cb))->
      let env' = None in (* TODO: build a proper environment if env <> None *)
      let s = (String.concat "." (List.map string_of_id idl)) in
      hov 2 (print_modtype env' mp locals seb ++ spc() ++ str "with" ++ spc() ++
	       str "Definition"++ spc() ++ str s ++ spc() ++  str ":="++ spc())
  | SEBwith(seb,With_module_body(idl,mp))->
      let s =(String.concat "." (List.map string_of_id idl)) in
      hov 2 (print_modtype env mp locals seb ++ spc() ++ str "with" ++ spc() ++
	       str "Module"++ spc() ++ str s ++ spc() ++ str ":="++ spc())

let rec print_modexpr env mp locals mexpr = match mexpr with
  | SEBident mp -> print_modpath locals mp
  | SEBfunctor (mbid,mty,mexpr) ->
      let mp' = MPbound mbid in
      let env' = Option.map
	(Modops.add_module (Modops.module_body_of_type mp' mty)) env in
      let typ = Option.default mty.typ_expr mty.typ_expr_alg in
      let locals' = (mbid, get_new_id locals (id_of_mbid mbid))::locals in
      (try Declaremods.process_module_seb_binding mbid typ with _ -> ());
      hov 2 (str "Functor" ++ spc() ++ str"(" ++ pr_id(id_of_mbid mbid) ++
	     str ":" ++ print_modtype env mp' locals typ ++
      str ")" ++ spc () ++ print_modexpr env' mp locals' mexpr)
  | SEBstruct struc ->
      let env' = Option.map
	(Modops.add_signature mp struc Mod_subst.empty_delta_resolver) env in
      hv 2 (str "Struct" ++ spc () ++ print_struct true env' mp struc ++
	    brk (1,-2) ++ str "End")
  | SEBapply _ ->
      let lapp = flatten_app mexpr [] in
      hov 3 (str"(" ++ prlist_with_sep spc (print_modpath locals) lapp ++ str")")
  | SEBwith (_,_)-> anomaly "Not available yet"


let rec printable_body dir =
  let dir = pop_dirpath dir in
    dir = empty_dirpath ||
    try
      match Nametab.locate_dir (qualid_of_dirpath dir) with
	  DirOpenModtype _ -> false
	| DirModule _ | DirOpenModule _ -> printable_body dir
	| _ -> true
    with
	Not_found -> true

(** Since we might play with nametab above, we should reset to prior
    state after the printing *)

let print_modexpr' env mp mexpr =
  States.with_state_protection (print_modexpr env mp []) mexpr
let print_modtype' env mp mty =
  States.with_state_protection (print_modtype env mp []) mty

let print_module' env mp with_body mb =
  let name = print_modpath [] mp in
  let body = match with_body, mb.mod_expr with
    | false, _
    | true, None -> mt()
    | true, Some mexpr ->
	spc () ++ str ":= " ++ print_modexpr' env mp mexpr
  in
  let modtype = brk (1,1) ++ str": " ++ print_modtype' env mp mb.mod_type
  in
  hv 0 (str "Module " ++ name ++ modtype ++ body)

exception ShortPrinting

let print_module with_body mp =
  let me = Global.lookup_module mp in
  try
    if !short then raise ShortPrinting;
    print_module' (Some (Global.env ())) mp with_body me ++ fnl ()
  with _ ->
    print_module' None mp with_body me ++ fnl ()

let print_modtype kn =
  let mtb = Global.lookup_modtype kn in
  let name = print_kn [] kn in
  hv 1
    (str "Module Type " ++ name ++ str " =" ++ spc () ++
     (try
	if !short then raise ShortPrinting;
	print_modtype' (Some (Global.env ())) kn mtb.typ_expr
      with _ ->
	print_modtype' None kn mtb.typ_expr))
