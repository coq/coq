(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)
(* Inlining and more liberal use of modules and module types by Claudio
   Sacerdoti, Nov 2004 *)
(* New structure-based model of modules and miscellaneous bug fixes by
   Élie Soubiran, from Feb 2008 *)

(* This file provides with various operations on modules and module types *)

open Errors
open Util
open Names
open Term
open Declarations
open Declareops
open Environ
open Entries
open Mod_subst

type signature_mismatch_error =
  | InductiveFieldExpected of mutual_inductive_body
  | DefinitionFieldExpected
  | ModuleFieldExpected
  | ModuleTypeFieldExpected
  | NotConvertibleInductiveField of Id.t
  | NotConvertibleConstructorField of Id.t
  | NotConvertibleBodyField
  | NotConvertibleTypeField of env * types * types
  | NotSameConstructorNamesField
  | NotSameInductiveNameInBlockField
  | FiniteInductiveFieldExpected of bool
  | InductiveNumbersFieldExpected of int
  | InductiveParamsNumberField of int
  | RecordFieldExpected of bool
  | RecordProjectionsExpected of Name.t list
  | NotEqualInductiveAliases
  | NoTypeConstraintExpected

type module_typing_error =
  | SignatureMismatch of Label.t * structure_field_body * signature_mismatch_error
  | LabelAlreadyDeclared of Label.t
  | ApplicationToNotPath of module_struct_entry
  | NotAFunctor of struct_expr_body
  | IncompatibleModuleTypes of module_type_body * module_type_body
  | NotEqualModulePaths of module_path * module_path
  | NoSuchLabel of Label.t
  | IncompatibleLabels of Label.t * Label.t
  | SignatureExpected of struct_expr_body
  | NotAModule of string
  | NotAModuleType of string
  | NotAConstant of Label.t
  | IncorrectWithConstraint of Label.t
  | GenerativeModuleExpected of Label.t
  | LabelMissing of Label.t * string
  | HigherOrderInclude

exception ModuleTypingError of module_typing_error

let error_existing_label l =
  raise (ModuleTypingError (LabelAlreadyDeclared l))

let error_application_to_not_path mexpr =
  raise (ModuleTypingError (ApplicationToNotPath mexpr))

let error_not_a_functor mtb =
  raise (ModuleTypingError (NotAFunctor mtb))

let error_incompatible_modtypes mexpr1 mexpr2 =
  raise (ModuleTypingError (IncompatibleModuleTypes (mexpr1,mexpr2)))

let error_not_equal_modpaths mp1 mp2 =
  raise (ModuleTypingError (NotEqualModulePaths (mp1,mp2)))

let error_signature_mismatch l spec why =
  raise (ModuleTypingError (SignatureMismatch (l,spec,why)))

let error_no_such_label l =
  raise (ModuleTypingError (NoSuchLabel l))

let error_incompatible_labels l l' =
  raise (ModuleTypingError (IncompatibleLabels (l,l')))

let error_signature_expected mtb =
  raise (ModuleTypingError (SignatureExpected mtb))

let error_not_a_module s =
  raise (ModuleTypingError (NotAModule s))

let error_not_a_constant l =
  raise (ModuleTypingError (NotAConstant l))

let error_incorrect_with_constraint l =
  raise (ModuleTypingError (IncorrectWithConstraint l))

let error_generative_module_expected l =
  raise (ModuleTypingError (GenerativeModuleExpected l))

let error_no_such_label_sub l l1 =
  raise (ModuleTypingError (LabelMissing (l,l1)))

let error_higher_order_include () =
  raise (ModuleTypingError HigherOrderInclude)

let destr_functor mtb =
  match mtb with
  | SEBfunctor (arg_id,arg_t,body_t) ->
      	    (arg_id,arg_t,body_t)
  | _ -> error_not_a_functor mtb

let is_functor = function
 | SEBfunctor (arg_id,arg_t,body_t) -> true
 | _ -> false

let module_body_of_type mp mtb = 
  { mod_mp = mp;
    mod_type = mtb.typ_expr;
    mod_type_alg = mtb.typ_expr_alg;
    mod_expr = None;
    mod_constraints = mtb.typ_constraints;
    mod_delta = mtb.typ_delta;
    mod_retroknowledge = []}

let check_modpath_equiv env mp1 mp2 = 
  if mp_eq mp1 mp2 then () else
    let mb1=lookup_module  mp1 env in
    let mb2=lookup_module mp2 env in
      if mp_eq (mp_of_delta mb1.mod_delta mp1) (mp_of_delta mb2.mod_delta mp2)
      then ()
      else error_not_equal_modpaths mp1 mp2
	
let rec subst_with_body sub = function
  | With_module_body(id,mp) ->
      With_module_body(id,subst_mp sub mp)
  | With_definition_body(id,cb) ->
      With_definition_body( id,subst_const_body sub cb)

and subst_modtype sub do_delta mtb=
  let mp = subst_mp sub mtb.typ_mp in
  let sub = add_mp mtb.typ_mp mp empty_delta_resolver sub in
  let typ_expr' = subst_struct_expr sub do_delta mtb.typ_expr in
  let typ_alg' = 
    Option.smartmap 
      (subst_struct_expr sub (fun x y-> x)) mtb.typ_expr_alg in
  let mtb_delta = do_delta mtb.typ_delta sub in
    if typ_expr'==mtb.typ_expr && 
      typ_alg'==mtb.typ_expr_alg && mp==mtb.typ_mp then
	mtb
    else
      {mtb with 
	 typ_mp = mp;
	 typ_expr = typ_expr';
	 typ_expr_alg = typ_alg';
	 typ_delta = mtb_delta}
	
and subst_structure sub do_delta sign = 
  let subst_body = function
      SFBconst cb -> 
	SFBconst (subst_const_body sub cb)
    | SFBmind mib -> 
	SFBmind (subst_mind sub mib)
    | SFBmodule mb -> 
	SFBmodule (subst_module sub do_delta mb)
    | SFBmodtype mtb -> 
	SFBmodtype (subst_modtype sub do_delta mtb)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign

and subst_module sub do_delta mb =
  let mp = subst_mp sub mb.mod_mp in
  let sub = if is_functor mb.mod_type && not (mp_eq mp mb.mod_mp) then
    add_mp mb.mod_mp mp
      empty_delta_resolver sub else sub in 
  let id_delta = (fun x y-> x) in
  let mtb',me' = 
    let mtb = subst_struct_expr sub do_delta mb.mod_type in 
      match mb.mod_expr with
	  None -> mtb,None
	| Some me -> if me==mb.mod_type then
	    mtb,Some mtb
	  else mtb,Option.smartmap 
	    (subst_struct_expr sub id_delta) mb.mod_expr
  in
  let typ_alg' = Option.smartmap 
    (subst_struct_expr sub id_delta) mb.mod_type_alg in
  let mb_delta = do_delta mb.mod_delta sub in
    if mtb'==mb.mod_type && mb.mod_expr == me' 
      && mb_delta == mb.mod_delta && mp == mb.mod_mp
    then mb else
      { mb with
	  mod_mp = mp;
	  mod_expr = me';
	  mod_type_alg = typ_alg';
	  mod_type=mtb'; 
	  mod_delta = mb_delta}

and subst_struct_expr sub do_delta = function
    | SEBident mp -> SEBident (subst_mp sub mp)
    | SEBfunctor (mbid, mtb, meb') -> 
	SEBfunctor(mbid,subst_modtype sub do_delta mtb
		     ,subst_struct_expr sub do_delta meb')
    | SEBstruct (str)->
	SEBstruct( subst_structure sub do_delta str)
    | SEBapply (meb1,meb2,cst)->
	SEBapply(subst_struct_expr sub do_delta meb1,
		 subst_struct_expr sub do_delta meb2,
		 cst)
    | SEBwith (meb,wdb)-> 
	SEBwith(subst_struct_expr sub do_delta meb,
		subst_with_body sub wdb)

let subst_signature subst =
  subst_structure subst 
    (fun resolver subst-> subst_codom_delta_resolver subst resolver)

let subst_struct_expr subst = 
  subst_struct_expr subst
    (fun resolver subst-> subst_codom_delta_resolver subst resolver)

(* spiwack: here comes the function which takes care of importing 
   the retroknowledge declared in the library *)
(* lclrk : retroknowledge_action list, rkaction : retroknowledge action *)
let add_retroknowledge mp =
  let perform rkaction env =
    match rkaction with
      | Retroknowledge.RKRegister (f, e) ->
	  Environ.register env f 
	  (match e with 
	    | Const kn -> kind_of_term (mkConst kn)
	    | Ind ind -> kind_of_term (mkInd ind)
	    | _ -> anomaly ~label:"Modops.add_retroknowledge" (Pp.str "had to import an unsupported kind of term"))
  in
  fun lclrk env ->
  (* The order of the declaration matters, for instance (and it's at the
     time this comment is being written, the only relevent instance) the
     int31 type registration absolutely needs int31 bits to be registered.
     Since the local_retroknowledge is stored in reverse order (each new
     registration is added at the top of the list) we need a fold_right
     for things to go right (the pun is not intented). So we lose 
     tail recursivity, but the world will have exploded before any module
     imports 10 000 retroknowledge registration.*)
  List.fold_right perform lclrk env

let rec add_signature mp sign resolver env = 
  let add_one env (l,elem) =
    let kn = KerName.make2 mp l in
    match elem with
      | SFBconst cb ->
	Environ.add_constant (constant_of_delta_kn resolver kn) cb env
      | SFBmind mib ->
	Environ.add_mind (mind_of_delta_kn resolver kn) mib env
      | SFBmodule mb -> add_module mb env (* adds components as well *)
      | SFBmodtype mtb -> Environ.add_modtype mtb env
  in
    List.fold_left add_one env sign

and add_module mb env =
  let mp = mb.mod_mp in
  let env = Environ.shallow_add_module mb env in
  match mb.mod_type with
  | SEBstruct (sign) ->
    add_retroknowledge mp mb.mod_retroknowledge
      (add_signature mp sign mb.mod_delta env)
  | SEBfunctor _ -> env
  | _ ->
    anomaly ~label:"Modops"
      (Pp.str "the evaluation of the structure failed ")

let strengthen_const mp_from l cb resolver =
  match cb.const_body with
    | Def _ -> cb
    | _ ->
      let kn = KerName.make2 mp_from l in
      let con = constant_of_delta_kn resolver kn in
      { cb with
	const_body = Def (Lazyconstr.from_val (mkConst con));
	const_body_code = Cemitcodes.from_val (Cbytegen.compile_alias con)
      }

let rec strengthen_mod mp_from mp_to mb =
  if mp_in_delta mb.mod_mp mb.mod_delta then
    mb
  else
    match mb.mod_type with
     | SEBstruct (sign) ->
	 let resolve_out,sign_out =
           strengthen_sig mp_from sign mp_to mb.mod_delta
         in
	 { mb with
	   mod_expr = Some (SEBident mp_to);
	   mod_type = SEBstruct(sign_out);
	   mod_type_alg = mb.mod_type_alg;
	   mod_constraints = mb.mod_constraints;
	   mod_delta = add_mp_delta_resolver mp_from mp_to
	     (add_delta_resolver mb.mod_delta resolve_out);
	   mod_retroknowledge = mb.mod_retroknowledge }
     | SEBfunctor _ -> mb
     | _ ->
       anomaly ~label:"Modops"
         (Pp.str "the evaluation of the structure failed ")

and strengthen_sig mp_from sign mp_to resolver =
  match sign with
    | [] -> empty_delta_resolver,[]
    | (l,SFBconst cb) :: rest ->
	let item' = l,SFBconst (strengthen_const mp_from l cb resolver) in
	let resolve_out,rest' = strengthen_sig mp_from rest mp_to resolver in
	resolve_out,item'::rest'
    | (_,SFBmind _ as item):: rest ->
	let resolve_out,rest' = strengthen_sig mp_from rest mp_to resolver in
	resolve_out,item::rest'
    | (l,SFBmodule mb) :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let mb_out = strengthen_mod mp_from' mp_to' mb in
	let item' = l,SFBmodule (mb_out) in
	let resolve_out,rest' = strengthen_sig mp_from rest mp_to resolver in
	add_delta_resolver resolve_out mb.mod_delta, item':: rest'
    | (l,SFBmodtype mty as item) :: rest ->
	let resolve_out,rest' = strengthen_sig mp_from rest mp_to resolver in
	resolve_out,item::rest'

let strengthen mtb mp =
  if mp_in_delta mtb.typ_mp mtb.typ_delta then
    (* in this case mtb has already been strengthened*)
    mtb
  else
    match mtb.typ_expr with
      | SEBstruct (sign) ->
	  let resolve_out,sign_out =
	    strengthen_sig mtb.typ_mp sign mp mtb.typ_delta
          in
	  {mtb with
	    typ_expr = SEBstruct(sign_out);
	    typ_delta = add_delta_resolver mtb.typ_delta
	      (add_mp_delta_resolver mtb.typ_mp mp resolve_out)}
      | SEBfunctor _ -> mtb
      | _ ->
        anomaly ~label:"Modops"
          (Pp.str "the evaluation of the structure failed ")

let module_type_of_module mp mb =
  match mp with
      Some mp ->
	strengthen {
	  typ_mp = mp;
	  typ_expr = mb.mod_type;
	  typ_expr_alg = None;
	  typ_constraints = mb.mod_constraints;
	  typ_delta = mb.mod_delta} mp

    | None ->
	{typ_mp = mb.mod_mp;
	 typ_expr = mb.mod_type;
	 typ_expr_alg = None;
	 typ_constraints = mb.mod_constraints;
	 typ_delta = mb.mod_delta}

let inline_delta_resolver env inl mp mbid mtb delta =
  let constants = inline_of_delta inl mtb.typ_delta in
  let rec make_inline delta = function
    | [] -> delta
    | (lev,kn)::r ->
	let kn = replace_mp_in_kn (MPbound mbid) mp kn in
	let con = constant_of_delta_kn delta kn in
	try
	  let constant = lookup_constant con env in
	  let l = make_inline delta r in
	  match constant.const_body with
	    | Undef _ | OpaqueDef _ -> l
	    | Def body ->
	      let constr = Lazyconstr.force body in
	      add_inline_delta_resolver kn (lev, Some constr) l
	with Not_found ->
	  error_no_such_label_sub (con_label con)
	    (string_of_mp (con_modpath con))
  in
  make_inline delta constants

let rec strengthen_and_subst_mod mb subst mp_from mp_to resolver =
  match mb.mod_type with
    | SEBstruct str ->
      let mb_is_an_alias = mp_in_delta mb.mod_mp mb.mod_delta in
      if mb_is_an_alias then
	subst_module subst
	  (fun resolver subst-> subst_dom_delta_resolver subst resolver) mb
      else
	let resolver,new_sig =
	  strengthen_and_subst_struct str subst
	    mp_from mp_from mp_to false false mb.mod_delta
	in
	{mb with
	  mod_mp = mp_to;
	  mod_expr = Some (SEBident mp_from);
	  mod_type = SEBstruct(new_sig);
	  mod_delta = add_mp_delta_resolver mp_to mp_from resolver}
    | SEBfunctor(arg_id,arg_b,body) ->
      let subst = add_mp mb.mod_mp mp_to empty_delta_resolver subst in
      subst_module subst
	(fun resolver subst-> subst_dom_codom_delta_resolver subst resolver) mb
    | _ ->
      anomaly ~label:"Modops"
        (Pp.str "the evaluation of the structure failed ")

and strengthen_and_subst_struct
    str subst mp_alias mp_from mp_to alias incl resolver =
  match str with
    | [] -> empty_delta_resolver,[]
    | (l,SFBconst cb) :: rest ->
	let item' = if alias then 
	  (* case alias no strengthening needed*)
	  l,SFBconst (subst_const_body subst cb) 
	else 
	  l,SFBconst (strengthen_const mp_from l
			(subst_const_body subst cb) resolver)
	in
	let resolve_out,rest' =
	  strengthen_and_subst_struct rest subst
	    mp_alias mp_from mp_to alias incl resolver in
	if incl then
	    (* If we are performing an inclusion we need to add
	       the fact that the constant mp_to.l is \Delta-equivalent
	       to resolver(mp_from.l) *)
	  let kn_from = KerName.make2 mp_from l in
	  let kn_to = KerName.make2 mp_to l in
	  let old_name = kn_of_delta resolver kn_from in
	  (add_kn_delta_resolver kn_to old_name resolve_out),
	  item'::rest'
	else
	    (*In this case the fact that the constant mp_to.l is 
	      \Delta-equivalent to resolver(mp_from.l) is already known
	       because resolve_out contains mp_to maps to resolver(mp_from)*)
	  resolve_out,item'::rest'
    | (l,SFBmind mib) :: rest ->
	(*Same as constant*)
	let item' = l,SFBmind (subst_mind subst mib) in
	let resolve_out,rest' =
	  strengthen_and_subst_struct rest subst
	    mp_alias mp_from mp_to alias incl resolver in
	if incl then
	  let kn_from = KerName.make2 mp_from l in
	  let kn_to = KerName.make2 mp_to l in
	  let old_name = kn_of_delta resolver kn_from in
	  (add_kn_delta_resolver kn_to old_name resolve_out),
	  item'::rest'
	else
	  resolve_out,item'::rest'
    | (l,SFBmodule mb) :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let mb_out = if alias then 
	  subst_module subst 
	  (fun resolver subst -> subst_dom_delta_resolver subst resolver) mb 
	else
	  strengthen_and_subst_mod
	    mb subst mp_from' mp_to' resolver
	in
	let item' = l,SFBmodule (mb_out) in
	let resolve_out,rest' =
	  strengthen_and_subst_struct rest subst
	    mp_alias mp_from mp_to alias incl resolver in
	  (* if mb is a functor we should not derive new equivalences
	     on names, hence we add the fact that the functor can only
	     be equivalent to itself. If we adopt an applicative
	     semantic for functor this should be changed.*)
	  if is_functor mb_out.mod_type then 
	    (add_mp_delta_resolver 
	       mp_to' mp_to' resolve_out),item':: rest' 
	  else
	    add_delta_resolver resolve_out mb_out.mod_delta,
	item':: rest'
    | (l,SFBmodtype mty) :: rest -> 
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let subst' = add_mp mp_from' mp_to' empty_delta_resolver subst in
	let mty = subst_modtype subst' 
	  (fun resolver subst -> subst_dom_codom_delta_resolver subst' resolver) mty in
	let resolve_out,rest' = strengthen_and_subst_struct rest subst
	    mp_alias mp_from mp_to alias incl resolver
        in
	(add_mp_delta_resolver mp_to' mp_to' resolve_out),
        (l,SFBmodtype mty)::rest'


(* Let P be a module path when we write "Module M:=P." or "Module M. Include P. End M."
   we need to perform two operations to compute the body of M. The first one is applying
   the substitution {P <- M} on the type of P and the second one is strenghtening. *)
let strengthen_and_subst_mb mb mp include_b =
    match mb.mod_type with
	SEBstruct str ->
	  let mb_is_an_alias = mp_in_delta mb.mod_mp mb.mod_delta in
	    (*if mb.mod_mp is an alias then the strengthening is useless 
	      (i.e. it is already done)*)
	  let mp_alias = mp_of_delta mb.mod_delta mb.mod_mp in
	  let subst_resolver = map_mp mb.mod_mp mp empty_delta_resolver in
	  let new_resolver = 
	    add_mp_delta_resolver mp mp_alias
	      (subst_dom_delta_resolver subst_resolver mb.mod_delta) in
	  let subst = map_mp mb.mod_mp mp new_resolver in 
	  let resolver_out,new_sig = 
	    strengthen_and_subst_struct str subst
	     mp_alias mb.mod_mp mp mb_is_an_alias include_b mb.mod_delta 
	  in
	    {mb with 
	       mod_mp = mp;
	       mod_type = SEBstruct(new_sig);
	       mod_expr = Some (SEBident mb.mod_mp);
	       mod_delta = if include_b then resolver_out 
	       else add_delta_resolver new_resolver resolver_out}
      | SEBfunctor(arg_id,argb,body) ->
	  let subst = map_mp mb.mod_mp mp empty_delta_resolver in
	  subst_module subst 
	    (fun resolver subst -> subst_dom_codom_delta_resolver subst resolver) mb 
      | _ -> anomaly ~label:"Modops" (Pp.str "the evaluation of the structure failed ")


let subst_modtype_and_resolver mtb mp =
  let subst = (map_mp mtb.typ_mp mp empty_delta_resolver) in
  let new_delta = subst_dom_codom_delta_resolver subst mtb.typ_delta in 
  let full_subst = (map_mp mtb.typ_mp mp new_delta) in
    subst_modtype full_subst
      (fun resolver subst -> subst_dom_codom_delta_resolver subst resolver) mtb

let rec is_bounded_expr l = function
  | SEBident mp -> List.mem mp l
  | SEBapply (fexpr,mexpr,_) ->  
      is_bounded_expr l mexpr || is_bounded_expr l fexpr
  | _ -> false

let rec clean_struct l = function
  | (lab,SFBmodule mb) as field -> 
      let clean_typ = clean_expr l mb.mod_type in 
      let clean_impl = 
	begin try
	  if (is_bounded_expr l (Option.get mb.mod_expr)) then
	    Some clean_typ
	  else  Some (clean_expr l (Option.get mb.mod_expr))
	with
	    Option.IsNone -> None 
	end in
	  if clean_typ==mb.mod_type && clean_impl==mb.mod_expr then
	    field 
	  else 
	    (lab,SFBmodule {mb with 
			      mod_type=clean_typ;
			      mod_expr=clean_impl})
  | field -> field
      
and clean_expr l = function
 | SEBfunctor (mbid,sigt,str) as s->
     let str_clean = clean_expr l str in
     let sig_clean = clean_expr l sigt.typ_expr in 
       if  str_clean == str && Int.equal (Pervasives.compare sig_clean sigt.typ_expr) 0 then (** FIXME **)
	 s else SEBfunctor (mbid,{sigt with typ_expr=sig_clean},str_clean)
  | SEBstruct str as s->
      let str_clean = Util.List.smartmap (clean_struct l) str in 
	if  str_clean == str then s else SEBstruct(str_clean)
  |  str -> str 

let rec collect_mbid l = function
  | SEBfunctor (mbid,sigt,str) as s->
      let str_clean = collect_mbid ((MPbound mbid)::l) str in 
	if  str_clean == str then s else 
      SEBfunctor (mbid,sigt,str_clean)
  | SEBstruct str as s->
      let str_clean = Util.List.smartmap (clean_struct l) str in 
	if  str_clean == str then s else SEBstruct(str_clean)
  |  _ -> anomaly ~label:"Modops" (Pp.str "the evaluation of the structure failed ")
       
       
let clean_bounded_mod_expr = function
  | SEBfunctor _ as str -> 
      let str_clean = collect_mbid [] str in 
	if  str_clean == str then str else str_clean
  | str -> str

let rec join_module_body mb =
  Option.iter join_struct_expr_body mb.mod_expr;
  Option.iter join_struct_expr_body mb.mod_type_alg;
  join_struct_expr_body mb.mod_type
and join_structure_body struc =
  let join_body (l,body) = match body with
    | SFBconst sb -> join_constant_body sb
    | SFBmind _ -> ()
    | SFBmodule m -> join_module_body m
    | SFBmodtype m ->
         join_struct_expr_body m.typ_expr;
         Option.iter join_struct_expr_body m.typ_expr_alg in
  List.iter join_body struc;
and join_struct_expr_body = function
  | SEBfunctor (_,t,e) ->
      join_struct_expr_body t.typ_expr;
      Option.iter join_struct_expr_body t.typ_expr_alg;
      join_struct_expr_body e
  | SEBident mp -> ()
  | SEBstruct s -> join_structure_body s
  | SEBapply (mexpr,marg,u) ->
       join_struct_expr_body mexpr;
       join_struct_expr_body marg
  | SEBwith (seb,wdcl) ->
       join_struct_expr_body seb;
       match wdcl with
       | With_module_body _ -> ()
       | With_definition_body (_, sb) -> join_constant_body sb

let rec prune_module_body mb =
  let me, mta, mt = mb.mod_expr, mb.mod_type_alg, mb.mod_type in
  let me' = Option.smartmap prune_struct_expr_body me in
  let mta' = Option.smartmap prune_struct_expr_body mta in
  let mt' = prune_struct_expr_body mt in
  if me' == me && mta' == mta && mt' == mt then mb
  else {mb with mod_expr = me'; mod_type_alg = mta'; mod_type = mt'}
and prune_structure_body struc =
  let prune_body (l,body as orig) = match body with
    | SFBconst sb ->
        let sb' = prune_constant_body sb in
        if sb == sb' then orig else (l, SFBconst sb')
    | SFBmind _ -> orig
    | SFBmodule m ->
        let m' = prune_module_body m in
        if m == m' then orig else (l, SFBmodule m')
    | SFBmodtype m ->
        let te, te_alg = m.typ_expr, m.typ_expr_alg in
        let te' = prune_struct_expr_body te in
        let te_alg' =
          Option.smartmap prune_struct_expr_body te_alg in
        if te' == te && te_alg' == te_alg then orig
        else (l, SFBmodtype {m with typ_expr = te'; typ_expr_alg = te_alg'}) in
  CList.smartmap prune_body struc
and prune_struct_expr_body orig = match orig with
  | SEBfunctor (id,t,e) ->
      let te, ta = t.typ_expr, t.typ_expr_alg in
      let te' = prune_struct_expr_body te in
      let ta' = Option.smartmap prune_struct_expr_body ta in
      let e' = prune_struct_expr_body e in
      if te' == te && ta' == ta && e' == e then orig
      else SEBfunctor(id, {t with typ_expr = te'; typ_expr_alg = ta'}, e')
  | SEBident _ -> orig
  | SEBstruct s ->
      let s' = prune_structure_body s in
      if s' == s then orig else SEBstruct s'
  | SEBapply (mexpr,marg,u) ->
      let mexpr' = prune_struct_expr_body mexpr in
      let marg' = prune_struct_expr_body marg in
      if mexpr' == mexpr && marg' == marg then orig
      else SEBapply (mexpr', marg', u)
  | SEBwith (seb,wdcl) ->
      let seb' = prune_struct_expr_body seb in
      let wdcl' = match wdcl with
        | With_module_body _ -> wdcl
        | With_definition_body (id, sb) ->
            let sb' = prune_constant_body sb in
            if sb' == sb then wdcl else With_definition_body (id, sb') in
      if seb' == seb && wdcl' == wdcl then orig
      else SEBwith (seb', wdcl')
       
