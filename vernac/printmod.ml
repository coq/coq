(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Constr
open Context
open Pp
open Names
open Declarations
open Libnames
open Goptions

(** Note: there is currently two modes for printing modules.
    - The "short" one, that just prints the names of the fields.
    - The "rich" one, that also tries to print the types of the fields.
    The short version used to be the default behavior, but now we print
    types by default. The following option allows changing this.
*)

module Tag =
struct

  let definition = "module.definition"
  let keyword    = "module.keyword"

end

let tag t s = Pp.tag t s
let tag_definition s = tag Tag.definition s
let tag_keyword s = tag Tag.keyword s

type short = OnlyNames | WithContents

let short = ref false

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Short";"Module";"Printing"];
      optread  = (fun () -> !short) ;
      optwrite = ((:=) short) }

(** Each time we have to print a non-globally visible structure,
    we place its elements in a fake fresh namespace. *)

let mk_fake_top =
  let r = ref 0 in
  fun () -> incr r; Id.of_string ("FAKETOP"^(string_of_int !r))

let def s = tag_definition (str s)
let keyword s = tag_keyword (str s)

let get_new_id locals id =
  let rec get_id l id =
    let dir = DirPath.make [id] in
      if not (Nametab.exists_module dir || Nametab.exists_dir dir) then
        id
      else
        get_id (Id.Set.add id l) (Namegen.next_ident_away id l)
  in
  let avoid = List.fold_left (fun accu (_, id) -> Id.Set.add id accu) Id.Set.empty locals in
    get_id avoid id

(** Inductive declarations *)

open Reduction

let print_params env sigma params =
  if List.is_empty params then mt ()
  else Printer.pr_rel_context env sigma params ++ brk(1,2)

let print_constructors envpar sigma names types =
  let pc =
    prlist_with_sep (fun () -> brk(1,0) ++ str "| ")
      (fun (id,c) -> Id.print id ++ str " : " ++ Printer.pr_lconstr_env envpar sigma c)
      (Array.to_list (Array.map2 (fun n t -> (n,t)) names types))
  in
  hv 0 (str "  " ++ pc)

let build_ind_type mip =
  Inductive.type_of_inductive mip

let get_fields =
  let rec prodec_rec l subst c =
    match kind c with
    | Prod (na,t,c) ->
        let id = match na.binder_name with Name id -> id | Anonymous -> Id.of_string "_" in
        prodec_rec ((id,true,Vars.substl subst t)::l) (mkVar id::subst) c
    | LetIn (na,b,_,c) ->
        let id = match na.binder_name with Name id -> id | Anonymous -> Id.of_string "_" in
        prodec_rec ((id,false,Vars.substl subst b)::l) (mkVar id::subst) c
    | _               -> List.rev l
  in
  prodec_rec [] []

let print_fields envpar sigma cstrtypes =
  let fields = get_fields cstrtypes.(0) in
  hv 2 (str "{ " ++
    prlist_with_sep (fun () -> str ";" ++ brk(2,0))
      (fun (id,b,c) ->
        Id.print id ++ str (if b then " : " else " := ") ++
        Printer.pr_lconstr_env envpar sigma c) fields) ++ str" }"

let print_one_inductive env sigma isrecord mib ((_,i) as ind) =
  let u = Univ.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
  let mip = mib.mind_packets.(i) in
  let paramdecls = Inductive.inductive_paramdecls (mib,u) in
  let env_params, params = Namegen.make_all_rel_context_name_different env (Evd.from_env env) (EConstr.of_rel_context paramdecls) in
  let params = EConstr.Unsafe.to_rel_context params in
  let nparamdecls = Context.Rel.length params in
  let args = Context.Rel.instance_list mkRel 0 params in
  let arity = hnf_prod_applist_assum env nparamdecls (build_ind_type ((mib,mip),u)) args in
  let cstrtypes = Inductive.type_of_constructors (ind,u) (mib,mip) in
  let cstrtypes = Array.map (fun c -> hnf_prod_applist_assum env nparamdecls c args) cstrtypes in
  if isrecord then assert (Array.length cstrtypes = 1);
  let inst =
    if Declareops.inductive_is_polymorphic mib then
      Printer.pr_universe_instance sigma u
    else mt ()
  in
  hov 0 (
    Id.print mip.mind_typename ++ inst ++ brk(1,4) ++ print_params env sigma params ++
    str ": " ++ Printer.pr_lconstr_env env_params sigma arity ++ str " :=" ++
    if isrecord then str " " ++ Id.print mip.mind_consnames.(0) else mt()) ++
    if not isrecord then
      brk(0,2) ++ print_constructors env_params sigma mip.mind_consnames cstrtypes
    else
      brk(1,2) ++ print_fields env_params sigma cstrtypes

let pr_mutual_inductive_body env mind mib udecl =
  let inds = List.init (Array.length mib.mind_packets) (fun x -> (mind, x)) in
  let keyword, isrecord =
    let open Declarations in
    match mib.mind_finite with
    | Finite -> "Inductive", false
    | CoFinite -> "CoInductive", false
    | BiFinite ->
       match mib.mind_record with
       | FakeRecord when not !Flags.raw_print -> "Record", true
       | PrimRecord _ -> "Record", true
       | FakeRecord | NotRecord -> "Variant", false
  in
  let bl = Printer.universe_binders_with_opt_names
      (Declareops.inductive_polymorphic_context mib) udecl
  in
  let sigma = Evd.from_ctx (UState.of_binders bl) in

  hov 0 (def keyword ++ spc () ++
         prlist_with_sep (fun () -> fnl () ++ str"  with ")
           (print_one_inductive env sigma isrecord mib) inds ++ str "." ++
         Printer.pr_universes sigma ?variance:mib.mind_variance mib.mind_universes)

(** Modpaths *)

let rec print_local_modpath locals = function
  | MPbound mbid -> Id.print (Util.List.assoc_f MBId.equal mbid locals)
  | MPdot(mp,l) ->
      print_local_modpath locals mp ++ str "." ++ Label.print l
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

let nametab_register_dir obj_mp =
  let id = mk_fake_top () in
  let obj_dir = DirPath.make [id] in
  Nametab.(push_module (Until 1) obj_dir obj_mp)

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
      push (Label.to_id l) (GlobRef.ConstRef (Constant.make2 mp l))
    | SFBmind mib ->
      let mind = MutInd.make2 mp l in
      Array.iteri
        (fun i mip ->
          push mip.mind_typename (GlobRef.IndRef (mind,i));
          Array.iteri (fun j id -> push id (GlobRef.ConstructRef ((mind,i),j+1)))
            mip.mind_consnames)
        mib.mind_packets

(* TODO only import printing-relevant objects (or find a way to print without importing) *)
let import_module = Declaremods.import_module Libobject.unfiltered
let process_module_binding = Declaremods.process_module_binding

let nametab_register_module_body mp struc =
  (* If [mp] is a globally visible module, we simply import it *)
  try import_module ~export:Lib.Import mp
  with Not_found ->
    (* Otherwise we try to emulate an import by playing with nametab *)
    nametab_register_dir mp;
    List.iter (nametab_register_body mp DirPath.empty) struc

let get_typ_expr_alg mtb = match mtb.mod_type_alg with
  | Some (NoFunctor me) -> me
  | _ -> raise Not_found

let nametab_register_modparam mbid mtb =
  let id = MBId.to_id mbid in
  match mtb.mod_type with
  | MoreFunctor _ -> id (* functorial param : nothing to register *)
  | NoFunctor struc ->
    (* We first try to use the algebraic type expression if any,
       via a Declaremods function that converts back to module entries *)
    try
      let () = process_module_binding mbid (get_typ_expr_alg mtb) in
      id
    with e when CErrors.noncritical e ->
      (* Otherwise, we try to play with the nametab ourselves *)
      let mp = MPbound mbid in
      let check id = Nametab.exists_module (DirPath.make [id]) in
      let id = Namegen.next_ident_away_from id check in
      let dir = DirPath.make [id] in
      nametab_register_dir mp;
      List.iter (nametab_register_body mp dir) struc;
      id

let print_body is_impl extent env mp (l,body) =
  let name = Label.print l in
  hov 2 (match body with
    | SFBmodule _ -> keyword "Module" ++ spc () ++ name
    | SFBmodtype _ -> keyword "Module Type" ++ spc () ++ name
    | SFBconst cb ->
       let ctx = Declareops.constant_polymorphic_context cb in
      (match cb.const_body with
        | Def _ -> def "Definition" ++ spc ()
        | OpaqueDef _ when is_impl -> def "Theorem" ++ spc ()
        | _ -> def "Parameter" ++ spc ()) ++ name ++
      (match extent with
         | OnlyNames -> mt ()
         | WithContents ->
            let bl = Printer.universe_binders_with_opt_names ctx None in
            let sigma = Evd.from_ctx (UState.of_binders bl) in
            str " :" ++ spc () ++
            hov 0 (Printer.pr_ltype_env env sigma cb.const_type) ++
            (match cb.const_body with
              | Def l when is_impl ->
                spc () ++
                hov 2 (str ":= " ++
                       Printer.pr_lconstr_env env sigma l)
              | _ -> mt ()) ++ str "." ++
            Printer.pr_abstract_universe_ctx sigma ctx)
    | SFBmind mib ->
      match extent with
      | WithContents ->
        pr_mutual_inductive_body env (MutInd.make2 mp l) mib None
      | OnlyNames ->
        let keyword =
          let open Declarations in
          match mib.mind_finite with
          | Finite -> def "Inductive"
          | BiFinite -> def "Variant"
          | CoFinite -> def "CoInductive"
        in
        keyword ++ spc () ++ name)

let print_struct is_impl extent env mp struc =
  prlist_with_sep spc (print_body is_impl extent env mp) struc

let print_structure is_type extent env mp locals struc =
  let env' = Modops.add_structure mp struc Mod_subst.empty_delta_resolver env in
  nametab_register_module_body mp struc;
  let kwd = if is_type then "Sig" else "Struct" in
  hv 2 (keyword kwd ++ spc () ++ print_struct false extent env' mp struc ++
        brk (1,-2) ++ keyword "End")

let rec flatten_app mexpr l = match mexpr with
  | MEapply (mexpr, arg) -> flatten_app mexpr (arg::l)
  | MEident mp -> mp::l
  | MEwith _ -> assert false

let rec print_typ_expr extent env mp locals mty =
  match mty with
  | MEident kn -> print_kn locals kn
  | MEapply _ ->
      let lapp = flatten_app mty [] in
      let fapp = List.hd lapp in
      let mapp = List.tl lapp in
      hov 3 (str"(" ++ (print_kn locals fapp) ++ spc () ++
                 prlist_with_sep spc (print_modpath locals) mapp ++ str")")
  | MEwith(me,WithDef(idl,(c, _)))->
      let s = String.concat "." (List.map Id.to_string idl) in
      let body = match extent with
        | WithContents ->
            let sigma = Evd.from_env env in
            spc() ++ str ":=" ++ spc() ++ Printer.pr_lconstr_env env sigma c
        | OnlyNames ->
            mt() in
      hov 2 (print_typ_expr extent env mp locals me ++ spc() ++ str "with" ++ spc()
             ++ def "Definition"++ spc() ++ str s ++ body)
  | MEwith(me,WithMod(idl,mp'))->
      let s = String.concat "." (List.map Id.to_string idl) in
      let body = match extent with
        | WithContents ->
            spc() ++ str ":="++ spc() ++ print_modpath locals mp'
        | OnlyNames -> mt () in
      hov 2 (print_typ_expr extent env mp locals me ++ spc() ++ str "with" ++ spc() ++
             keyword "Module"++ spc() ++ str s ++ body)

let print_mod_expr env mp locals = function
  | MEident mp -> print_modpath locals mp
  | MEapply _ as me ->
      let lapp = flatten_app me [] in
      hov 3
        (str"(" ++ prlist_with_sep spc (print_modpath locals) lapp ++ str")")
  | MEwith _ -> assert false (* No 'with' syntax for modules *)

let rec print_functor fty fatom is_type extent env mp locals = function
  | NoFunctor me -> fatom is_type extent env mp locals me
  | MoreFunctor (mbid,mtb1,me2) ->
      let id = nametab_register_modparam mbid mtb1 in
      let mp1 = MPbound mbid in
      let pr_mtb1 = fty extent env mp1 locals mtb1 in
      let env' = Modops.add_module_type mp1 mtb1 env in
      let locals' = (mbid, get_new_id locals (MBId.to_id mbid))::locals in
      let kwd = if is_type then "Funsig" else "Functor" in
      hov 2
        (keyword kwd ++ spc () ++
         str "(" ++ Id.print id ++ str ":" ++ pr_mtb1 ++ str ")" ++
         spc() ++ print_functor fty fatom is_type extent env' mp locals' me2)

let rec print_expression x =
  print_functor
    print_modtype
    (function true -> print_typ_expr | false -> fun _ -> print_mod_expr) x

and print_signature x =
  print_functor print_modtype print_structure x

and print_modtype extent env mp locals mtb = match mtb.mod_type_alg with
  | Some me -> print_expression true extent env mp locals me
  | None -> print_signature true extent env mp locals mtb.mod_type

(** Since we might play with nametab above, we should reset to prior
    state after the printing *)

let print_expression' is_type extent env mp me =
  Vernacstate.System.protect
    (fun e -> print_expression is_type extent env mp [] e) me

let print_signature' is_type extent env mp me =
  Vernacstate.System.protect
    (fun e -> print_signature is_type extent env mp [] e) me

let unsafe_print_module extent env mp with_body mb =
  let name = print_modpath [] mp in
  let pr_equals = spc () ++ str ":= " in
  let body = match with_body, mb.mod_expr with
    | false, _
    | true, Abstract -> mt()
    | _, Algebraic me -> pr_equals ++ print_expression' false extent env mp me
    | _, Struct sign -> pr_equals ++ print_signature' false extent env mp sign
    | _, FullStruct -> pr_equals ++ print_signature' false extent env mp mb.mod_type
  in
  let modtype = match mb.mod_expr, mb.mod_type_alg with
    | FullStruct, _ -> mt ()
    | _, Some ty -> brk (1,1) ++ str": " ++ print_expression' true extent env mp ty
    | _, _ -> brk (1,1) ++ str": " ++ print_signature' true extent env mp mb.mod_type
  in
  hv 0 (keyword "Module" ++ spc () ++ name ++ modtype ++ body)

exception ShortPrinting

let print_module ~with_body mp =
  let me = Global.lookup_module mp in
  try
    if !short then raise ShortPrinting;
    unsafe_print_module WithContents
      (Global.env ()) mp with_body me ++ fnl ()
  with e when CErrors.noncritical e ->
    unsafe_print_module OnlyNames
      (Global.env ()) mp with_body me ++ fnl ()

let print_modtype kn =
  let mtb = Global.lookup_modtype kn in
  let name = print_kn [] kn in
  hv 1
    (keyword "Module Type" ++ spc () ++ name ++ str " =" ++ spc () ++
     try
      if !short then raise ShortPrinting;
      print_signature' true WithContents
        (Global.env ()) kn mtb.mod_type
     with e when CErrors.noncritical e ->
      print_signature' true OnlyNames
        (Global.env ()) kn mtb.mod_type)
