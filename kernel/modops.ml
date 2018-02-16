(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)
(* Inlining and more liberal use of modules and module types by Claudio
   Sacerdoti, Nov 2004 *)
(* New structure-based model of modules and miscellaneous bug fixes by
   Élie Soubiran, from Feb 2008 *)

(* This file provides with various operations on modules and module types *)

open Util
open Names
open Constr
open Declarations
open Declareops
open Environ
open Entries
open Mod_subst

(** {6 Errors } *)

type signature_mismatch_error =
  | InductiveFieldExpected of mutual_inductive_body
  | DefinitionFieldExpected
  | ModuleFieldExpected
  | ModuleTypeFieldExpected
  | NotConvertibleInductiveField of Id.t
  | NotConvertibleConstructorField of Id.t
  | NotConvertibleBodyField
  | NotConvertibleTypeField of env * types * types
  | CumulativeStatusExpected of bool
  | PolymorphicStatusExpected of bool
  | NotSameConstructorNamesField
  | NotSameInductiveNameInBlockField
  | FiniteInductiveFieldExpected of bool
  | InductiveNumbersFieldExpected of int
  | InductiveParamsNumberField of int
  | RecordFieldExpected of bool
  | RecordProjectionsExpected of Name.t list
  | NotEqualInductiveAliases
  | IncompatibleUniverses of Univ.univ_inconsistency
  | IncompatiblePolymorphism of env * types * types
  | IncompatibleConstraints of { got : Univ.AUContext.t; expect : Univ.AUContext.t }

type module_typing_error =
  | SignatureMismatch of
      Label.t * structure_field_body * signature_mismatch_error
  | LabelAlreadyDeclared of Label.t
  | ApplicationToNotPath of module_struct_entry
  | NotAFunctor
  | IsAFunctor
  | IncompatibleModuleTypes of module_type_body * module_type_body
  | NotEqualModulePaths of ModPath.t * ModPath.t
  | NoSuchLabel of Label.t
  | IncompatibleLabels of Label.t * Label.t
  | NotAModule of string
  | NotAModuleType of string
  | NotAConstant of Label.t
  | IncorrectWithConstraint of Label.t
  | GenerativeModuleExpected of Label.t
  | LabelMissing of Label.t * string
  | IncludeRestrictedFunctor of ModPath.t

exception ModuleTypingError of module_typing_error

let error_existing_label l =
  raise (ModuleTypingError (LabelAlreadyDeclared l))

let error_not_a_functor () =
  raise (ModuleTypingError NotAFunctor)

let error_is_a_functor () =
  raise (ModuleTypingError IsAFunctor)

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

let error_include_restricted_functor mp =
  raise (ModuleTypingError (IncludeRestrictedFunctor mp))

(** {6 Operations on functors } *)

let is_functor = function
  |NoFunctor _ -> false
  |MoreFunctor _ -> true

let destr_functor = function
  |NoFunctor _ -> error_not_a_functor ()
  |MoreFunctor (mbid,ty,x) -> (mbid,ty,x)

let destr_nofunctor = function
  |NoFunctor a -> a
  |MoreFunctor _ -> error_is_a_functor ()

let rec functor_smart_map fty f0 funct = match funct with
  |MoreFunctor (mbid,ty,e) ->
    let ty' = fty ty in
    let e' = functor_smart_map fty f0 e in
    if ty==ty' && e==e' then funct else MoreFunctor (mbid,ty',e')
  |NoFunctor a ->
    let a' = f0 a in if a==a' then funct else NoFunctor a'

let rec functor_iter fty f0 = function
  |MoreFunctor (_mbid,ty,e) -> fty ty; functor_iter fty f0 e
  |NoFunctor a -> f0 a

(** {6 Misc operations } *)

let module_type_of_module mb =
  { mb with mod_expr = (); mod_type_alg = None;
    mod_retroknowledge = ModTypeRK; }

let module_body_of_type mp mtb =
  { mtb with mod_expr = Abstract; mod_mp = mp;
      mod_retroknowledge = ModBodyRK []; }

let check_modpath_equiv env mp1 mp2 =
  if ModPath.equal mp1 mp2 then ()
  else
    let mp1' = mp_of_delta (lookup_module mp1 env).mod_delta mp1 in
    let mp2' = mp_of_delta (lookup_module mp2 env).mod_delta mp2 in
    if ModPath.equal mp1' mp2' then ()
    else error_not_equal_modpaths mp1 mp2

let implem_smartmap fs fa impl = match impl with
  |Struct e -> let e' = fs e in if e==e' then impl else Struct e'
  |Algebraic a -> let a' = fa a in if a==a' then impl else Algebraic a'
  |Abstract|FullStruct -> impl

let implem_iter fs fa impl = match impl with
  |Struct e -> fs e
  |Algebraic a -> fa a
  |Abstract|FullStruct -> ()

(** {6 Substitutions of modular structures } *)

let id_delta x _y = x

let subst_with_body sub = function
  |WithMod(id,mp) as orig ->
    let mp' = subst_mp sub mp in
    if mp==mp' then orig else WithMod(id,mp')
  |WithDef(id,(c,ctx)) as orig ->
    let c' = subst_mps sub c in
    if c==c' then orig else WithDef(id,(c',ctx))

let rec subst_structure sub do_delta sign =
  let subst_body ((l,body) as orig) = match body with
    |SFBconst cb ->
      let cb' = subst_const_body sub cb in
      if cb==cb' then orig else (l,SFBconst cb')
    |SFBmind mib ->
      let mib' = subst_mind_body sub mib in
      if mib==mib' then orig else (l,SFBmind mib')
    |SFBmodule mb ->
      let mb' = subst_module sub do_delta mb in
      if mb==mb' then orig else (l,SFBmodule mb')
    |SFBmodtype mtb ->
      let mtb' = subst_modtype sub do_delta mtb in
      if mtb==mtb' then orig else (l,SFBmodtype mtb')
  in
  List.Smart.map subst_body sign

and subst_retro : type a. Mod_subst.substitution -> a module_retroknowledge -> a module_retroknowledge =
  fun subst retro ->
    match retro with
    | ModTypeRK as r -> r
    | ModBodyRK l as r ->
      let l' = List.Smart.map (subst_retro_action subst) l in
      if l == l' then r else ModBodyRK l

and subst_body : 'a. _ -> _ -> (_ -> 'a -> 'a) -> _ -> 'a generic_module_body -> 'a generic_module_body =
  fun is_mod sub subst_impl do_delta mb ->
    let { mod_mp=mp; mod_expr=me; mod_type=ty; mod_type_alg=aty;
          mod_retroknowledge=retro; _ } = mb in
  let mp' = subst_mp sub mp in
  let sub =
    if ModPath.equal mp mp' then sub
    else if is_mod && not (is_functor ty) then sub
    else add_mp mp mp' empty_delta_resolver sub
  in
  let ty' = subst_signature sub do_delta ty in
  let me' = subst_impl sub me in
  let aty' = Option.Smart.map (subst_expression sub id_delta) aty in
  let retro' = subst_retro sub retro in
  let delta' = do_delta mb.mod_delta sub in
  if mp==mp' && me==me' && ty==ty' && aty==aty'
     && retro==retro' && delta'==mb.mod_delta
  then mb
  else
    { mb with
      mod_mp = mp';
      mod_expr = me';
      mod_type = ty';
      mod_type_alg = aty';
      mod_retroknowledge = retro';
      mod_delta = delta';
    }

and subst_module sub do_delta mb =
  subst_body true sub subst_impl do_delta mb

and subst_impl sub me =
  implem_smartmap
    (subst_signature sub id_delta) (subst_expression sub id_delta) me

and subst_modtype sub do_delta mtb = subst_body false sub (fun _ () -> ()) do_delta mtb

and subst_expr sub do_delta seb = match seb with
  |MEident mp ->
    let mp' = subst_mp sub mp in
    if mp==mp' then seb else MEident mp'
  |MEapply (meb1,mp2) ->
    let meb1' = subst_expr sub do_delta meb1 in
    let mp2' = subst_mp sub mp2 in
    if meb1==meb1' && mp2==mp2' then seb else MEapply(meb1',mp2')
  |MEwith (meb,wdb) ->
    let meb' = subst_expr sub do_delta meb in
    let wdb' = subst_with_body sub wdb in
    if meb==meb' && wdb==wdb' then seb else MEwith(meb',wdb')

and subst_expression sub do_delta =
  functor_smart_map
    (subst_modtype sub do_delta)
    (subst_expr sub do_delta)

and subst_signature sub do_delta =
  functor_smart_map
    (subst_modtype sub do_delta)
    (subst_structure sub do_delta)

let do_delta_dom reso sub = subst_dom_delta_resolver sub reso
let do_delta_codom reso sub = subst_codom_delta_resolver sub reso
let do_delta_dom_codom reso sub = subst_dom_codom_delta_resolver sub reso

let subst_signature subst = subst_signature subst do_delta_codom
let subst_structure subst = subst_structure subst do_delta_codom

(** {6 Adding a module in the environment } *)

let add_retroknowledge r env =
  match r with
  | ModBodyRK l -> List.fold_left Primred.add_retroknowledge env l

let rec add_structure mp sign resolver linkinfo env =
  let add_one env (l,elem) = match elem with
    |SFBconst cb ->
      let c = constant_of_delta_kn resolver (KerName.make mp l) in
      Environ.add_constant_key c cb linkinfo env
    |SFBmind mib ->
      let mind = mind_of_delta_kn resolver (KerName.make mp l) in
      let mib = 
	if mib.mind_private != None then 
	  { mib with mind_private = Some true }
	else mib
      in
      Environ.add_mind_key mind (mib,ref linkinfo) env
    |SFBmodule mb -> add_module mb linkinfo env (* adds components as well *)
    |SFBmodtype mtb -> Environ.add_modtype mtb env
  in
  List.fold_left add_one env sign

and add_module mb linkinfo env =
  let mp = mb.mod_mp in
  let env = Environ.shallow_add_module mb env in
  match mb.mod_type with
  |NoFunctor struc ->
    add_retroknowledge mb.mod_retroknowledge
      (add_structure mp struc mb.mod_delta linkinfo env)
  |MoreFunctor _ -> env

let add_linked_module mb linkinfo env =
  add_module mb linkinfo env

let add_structure mp sign resolver env =
  add_structure mp sign resolver no_link_info env

let add_module mb env =
  add_module mb no_link_info env

let add_module_type mp mtb env =
  add_module (module_body_of_type mp mtb) env

(** {6 Strengtening } *)

let strengthen_const mp_from l cb resolver =
  match cb.const_body with
  |Def _ -> cb
  |_ ->
    let kn = KerName.make mp_from l in
    let con = constant_of_delta_kn resolver kn in
    let u =
      match cb.const_universes with
      | Monomorphic_const _ -> Univ.Instance.empty
      | Polymorphic_const ctx -> Univ.make_abstract_instance ctx
    in
      { cb with
        const_body = Def (Mod_subst.from_val (mkConstU (con,u)));
        const_private_poly_univs = None;
	const_body_code = Some (Cemitcodes.from_val (Cbytegen.compile_alias con)) }

let rec strengthen_mod mp_from mp_to mb =
  if mp_in_delta mb.mod_mp mb.mod_delta then mb
  else match mb.mod_type with
  |NoFunctor struc ->
    let reso,struc' = strengthen_sig mp_from struc mp_to mb.mod_delta in
    { mb with
      mod_expr = Algebraic (NoFunctor (MEident mp_to));
      mod_type = NoFunctor struc';
      mod_delta =
        add_mp_delta_resolver mp_from mp_to
	  (add_delta_resolver mb.mod_delta reso) }
  |MoreFunctor _ -> mb

and strengthen_sig mp_from struc mp_to reso = match struc with
  |[] -> empty_delta_resolver,[]
  |(l,SFBconst cb) :: rest ->
    let item' = l,SFBconst (strengthen_const mp_from l cb reso) in
    let reso',rest' = strengthen_sig mp_from rest mp_to reso in
    reso',item'::rest'
  |(_,SFBmind _ as item):: rest ->
    let reso',rest' = strengthen_sig mp_from rest mp_to reso in
    reso',item::rest'
  |(l,SFBmodule mb) :: rest ->
    let mp_from' = MPdot (mp_from,l) in
    let mp_to' = MPdot(mp_to,l) in
    let mb' = strengthen_mod mp_from' mp_to' mb in
    let item' = l,SFBmodule mb' in
    let reso',rest' = strengthen_sig mp_from rest mp_to reso in
    add_delta_resolver reso' mb.mod_delta, item':: rest'
  |(_l,SFBmodtype _mty as item) :: rest ->
    let reso',rest' = strengthen_sig mp_from rest mp_to reso in
    reso',item::rest'

let strengthen mtb mp =
  (* Has mtb already been strengthened ? *)
  if mp_in_delta mtb.mod_mp mtb.mod_delta then mtb
  else match mtb.mod_type with
  |NoFunctor struc ->
    let reso',struc' = strengthen_sig mtb.mod_mp struc mp mtb.mod_delta in
    { mtb with
      mod_type = NoFunctor struc';
      mod_delta =
        add_delta_resolver mtb.mod_delta
	  (add_mp_delta_resolver mtb.mod_mp mp reso') }
  |MoreFunctor _ -> mtb

let inline_delta_resolver env inl mp mbid mtb delta =
  let constants = inline_of_delta inl mtb.mod_delta in
  let rec make_inline delta = function
    | [] -> delta
    | (lev,kn)::r ->
	let kn = replace_mp_in_kn (MPbound mbid) mp kn in
	let con = constant_of_delta_kn delta kn in
	try
	  let constant = lookup_constant con env in
	  let l = make_inline delta r in
	  match constant.const_body with
            | Undef _ | OpaqueDef _ | Primitive _ -> l
	    | Def body ->
	      let constr = Mod_subst.force_constr body in
              let ctx = Declareops.constant_polymorphic_context constant in
              let constr = Univ.{univ_abstracted_value=constr; univ_abstracted_binder=ctx} in
              add_inline_delta_resolver kn (lev, Some constr) l
	with Not_found ->
	  error_no_such_label_sub (Constant.label con)
	    (ModPath.to_string (Constant.modpath con))
  in
  make_inline delta constants

let rec strengthen_and_subst_mod mb subst mp_from mp_to =
  match mb.mod_type with
  |NoFunctor struc ->
    let mb_is_an_alias = mp_in_delta mb.mod_mp mb.mod_delta in
    if mb_is_an_alias then subst_module subst do_delta_dom mb
    else
      let reso',struc' =
	strengthen_and_subst_struct struc subst
	  mp_from mp_to false false mb.mod_delta
      in
      { mb with
	mod_mp = mp_to;
	mod_expr = Algebraic (NoFunctor (MEident mp_from));
	mod_type = NoFunctor struc';
	mod_delta = add_mp_delta_resolver mp_to mp_from reso' }
  |MoreFunctor _ ->
    let subst = add_mp mb.mod_mp mp_to empty_delta_resolver subst in
    subst_module subst do_delta_dom mb

and strengthen_and_subst_struct str subst mp_from mp_to alias incl reso =
  match str with
    | [] -> empty_delta_resolver,[]
    | (l,SFBconst cb) as item :: rest ->
        let cb' = subst_const_body subst cb in
        let cb' =
          if alias then cb'
          else strengthen_const mp_from l cb' reso
        in
        let item' = if cb' == cb then item else (l, SFBconst cb') in
	let reso',rest' =
	  strengthen_and_subst_struct rest subst mp_from mp_to alias incl reso
        in
        let str' =
          if rest' == rest && item' == item then str
          else item' :: rest'
        in
	if incl then
          (* If we are performing an inclusion we need to add
             the fact that the constant mp_to.l is \Delta-equivalent
             to reso(mp_from.l) *)
          let kn_from = KerName.make mp_from l in
          let kn_to = KerName.make mp_to l in
          let old_name = kn_of_delta reso kn_from in
	  add_kn_delta_resolver kn_to old_name reso', str'
	else
	  (* In this case the fact that the constant mp_to.l is
	     \Delta-equivalent to resolver(mp_from.l) is already known
	     because reso' contains mp_to maps to reso(mp_from) *)
	  reso', str'
    | (l,SFBmind mib) as item :: rest ->
        let mib' = subst_mind_body subst mib in
        let item' = if mib' == mib then item else (l, SFBmind mib') in
	let reso',rest' =
	  strengthen_and_subst_struct rest subst mp_from mp_to alias incl reso
        in
        let str' =
          if rest' == rest && item' == item then str
          else item' :: rest'
        in
	(* Same as constant *)
	if incl then
          let kn_from = KerName.make mp_from l in
          let kn_to = KerName.make mp_to l in
	  let old_name = kn_of_delta reso kn_from in
          add_kn_delta_resolver kn_to old_name reso', str'
	else
          reso', str'
    | (l,SFBmodule mb) as item :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot (mp_to,l) in
	let mb' = if alias then
	  subst_module subst do_delta_dom mb
	else
	  strengthen_and_subst_mod mb subst mp_from' mp_to'
	in
        let item' = if mb' == mb then item else (l, SFBmodule mb') in
	let reso',rest' =
	  strengthen_and_subst_struct rest subst mp_from mp_to alias incl reso
        in
        let str' =
          if rest' == rest && item' == item then str
          else item' :: rest'
        in
        (* if mb is a functor we should not derive new equivalences
           on names, hence we add the fact that the functor can only
           be equivalent to itself. If we adopt an applicative
           semantic for functor this should be changed.*)
	if is_functor mb'.mod_type then
          add_mp_delta_resolver mp_to' mp_to' reso', str'
	else
          add_delta_resolver reso' mb'.mod_delta, str'
    | (l,SFBmodtype mty) as item :: rest ->
	let mp_from' = MPdot (mp_from,l) in
	let mp_to' = MPdot(mp_to,l) in
	let subst' = add_mp mp_from' mp_to' empty_delta_resolver subst in
	let mty' = subst_modtype subst'
	  (fun resolver _ -> subst_dom_codom_delta_resolver subst' resolver)
          mty
        in
        let item' = if mty' == mty then item else (l, SFBmodtype mty') in
	let reso',rest' =
          strengthen_and_subst_struct rest subst mp_from mp_to alias incl reso
        in
        let str' =
          if rest' == rest && item' == item then str
          else item' :: rest'
        in
	add_mp_delta_resolver mp_to' mp_to' reso', str'


(** Let P be a module path when we write:
     "Module M:=P." or "Module M. Include P. End M."
    We need to perform two operations to compute the body of M.
    - The first one is applying the substitution {P <- M} on the type of P
    - The second one is strenghtening. *)

let strengthen_and_subst_mb mb mp include_b = match mb.mod_type with
  |NoFunctor struc ->
    let mb_is_an_alias = mp_in_delta mb.mod_mp mb.mod_delta in
    (* if mb.mod_mp is an alias then the strengthening is useless
       (i.e. it is already done)*)
    let mp_alias = mp_of_delta mb.mod_delta mb.mod_mp in
    let subst_resolver = map_mp mb.mod_mp mp empty_delta_resolver in
    let new_resolver =
      add_mp_delta_resolver mp mp_alias
	(subst_dom_delta_resolver subst_resolver mb.mod_delta)
    in
    let subst = map_mp mb.mod_mp mp new_resolver in
    let reso',struc' =
      strengthen_and_subst_struct struc subst
	mb.mod_mp mp mb_is_an_alias include_b mb.mod_delta
    in
    { mb with
      mod_mp = mp;
      mod_type = NoFunctor struc';
      mod_expr = Algebraic (NoFunctor (MEident mb.mod_mp));
      mod_delta =
        if include_b then reso'
	else add_delta_resolver new_resolver reso' }
  |MoreFunctor _ ->
    let subst = map_mp mb.mod_mp mp empty_delta_resolver in
    subst_module subst do_delta_dom_codom mb

let subst_modtype_and_resolver mtb mp =
  let subst = map_mp mtb.mod_mp mp empty_delta_resolver in
  let new_delta = subst_dom_codom_delta_resolver subst mtb.mod_delta in
  let full_subst = map_mp mtb.mod_mp mp new_delta in
  subst_modtype full_subst do_delta_dom_codom mtb

(** {6 Cleaning a module expression from bounded parts }

     For instance:
       functor(X:T)->struct module M:=X end)
     becomes:
       functor(X:T)->struct module M:=<content of T> end)
*)

let rec is_bounded_expr l = function
  | MEident (MPbound mbid) -> MBIset.mem mbid l
  | MEapply (fexpr,mp) ->
      is_bounded_expr l (MEident mp) || is_bounded_expr l fexpr
  | _ -> false

let rec clean_module_body l mb =
  let impl, typ = mb.mod_expr, mb.mod_type in
  let typ' = clean_signature l typ in
  let impl' = match impl with
    | Algebraic (NoFunctor m) when is_bounded_expr l m -> FullStruct
    | _ -> implem_smartmap (clean_signature l) (clean_expression l) impl
  in
  if typ==typ' && impl==impl' then mb
  else { mb with mod_type=typ'; mod_expr=impl' }

and clean_module_type l mb =
  let (), typ = mb.mod_expr, mb.mod_type in
  let typ' = clean_signature l typ in
  if typ==typ' then mb
  else { mb with mod_type=typ' }

and clean_field l field = match field with
  |(lab,SFBmodule mb) ->
    let mb' = clean_module_body l mb in
    if mb==mb' then field else (lab,SFBmodule mb')
  |_ -> field

and clean_structure l = List.Smart.map (clean_field l)

and clean_signature l =
  functor_smart_map (clean_module_type l) (clean_structure l)

and clean_expression l =
  functor_smart_map (clean_module_type l) (fun me -> me)

let rec collect_mbid l sign =  match sign with
  |MoreFunctor (mbid,ty,m) ->
    let m' = collect_mbid (MBIset.add mbid l) m in
    if m==m' then sign else MoreFunctor (mbid,ty,m')
  |NoFunctor struc ->
    let struc' = clean_structure l struc in
    if struc==struc' then sign else NoFunctor struc'

let clean_bounded_mod_expr sign =
  if is_functor sign then collect_mbid MBIset.empty sign else sign

(** {6 Stm machinery } *)
let join_constant_body except otab cb =
  match cb.const_body with
  | OpaqueDef o ->
      (match Opaqueproof.uuid_opaque otab o with
      | Some uuid when not(Future.UUIDSet.mem uuid except) ->
          Opaqueproof.join_opaque otab o
      | _ -> ())
  | _ -> ()

let join_structure except otab s =
  let rec join_module : 'a. 'a generic_module_body -> unit = fun mb ->
    Option.iter join_expression mb.mod_type_alg;
    join_signature mb.mod_type
  and join_field (_l,body) = match body with
    |SFBconst sb -> join_constant_body except otab sb
    |SFBmind _ -> ()
    |SFBmodule m ->
      implem_iter join_signature join_expression m.mod_expr;
      join_module m
    |SFBmodtype m -> join_module m
  and join_structure struc = List.iter join_field struc
  and join_signature sign =
    functor_iter join_module join_structure sign
  and join_expression me = functor_iter join_module (fun _ -> ()) me in
  join_structure s

