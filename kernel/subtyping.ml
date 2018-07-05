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

(* This module checks subtyping of module types *)

(*i*)
open Names
open Univ
open Util
open Constr
open Declarations
open Declareops
open Reduction
open Inductive
open Modops
open Mod_subst
(*i*)

(* This local type is used to subtype a constant with a constructor or
   an inductive type. It can also be useful to allow reorderings in
   inductive types *)
type namedobject =
  | Constant of constant_body
  | IndType of inductive * mutual_inductive_body
  | IndConstr of constructor * mutual_inductive_body

type namedmodule =
  | Module of module_body
  | Modtype of module_type_body

(* adds above information about one mutual inductive: all types and
   constructors *)

let add_mib_nameobjects mp l mib map =
  let ind = MutInd.make2 mp l in
  let add_mip_nameobjects j oib map =
    let ip = (ind,j) in
    let map =
      Array.fold_right_i
      (fun i id map ->
        Label.Map.add (Label.of_id id) (IndConstr((ip,i+1), mib)) map)
      oib.mind_consnames
      map
    in
      Label.Map.add (Label.of_id oib.mind_typename) (IndType (ip, mib)) map
  in
  Array.fold_right_i add_mip_nameobjects mib.mind_packets map


(* creates (namedobject/namedmodule) map for the whole signature *)

type labmap = { objs : namedobject Label.Map.t; mods : namedmodule Label.Map.t }

let empty_labmap = { objs = Label.Map.empty; mods = Label.Map.empty }

let get_obj mp map l =
  try Label.Map.find l map.objs
  with Not_found -> error_no_such_label_sub l (ModPath.to_string mp)

let get_mod mp map l =
  try Label.Map.find l map.mods
  with Not_found -> error_no_such_label_sub l (ModPath.to_string mp)

let make_labmap mp list =
  let add_one (l,e) map =
   match e with
    | SFBconst cb -> { map with objs = Label.Map.add l (Constant cb) map.objs }
    | SFBmind mib -> { map with objs = add_mib_nameobjects mp l mib map.objs }
    | SFBmodule mb -> { map with mods = Label.Map.add l (Module mb) map.mods }
    | SFBmodtype mtb -> { map with mods = Label.Map.add l (Modtype mtb) map.mods }
  in
  CList.fold_right add_one list empty_labmap


let check_conv_error error why cst poly f env a1 a2 =
  try 
    let cst' = f env (Environ.universes env) a1 a2 in
      if poly then 
	if Constraint.is_empty cst' then cst
	else error (IncompatiblePolymorphism (env, a1, a2))
      else Constraint.union cst cst'
  with NotConvertible -> error why
     | Univ.UniverseInconsistency e -> error (IncompatibleUniverses e)

let check_polymorphic_instance error env auctx1 auctx2 =
  if not (Univ.AUContext.size auctx1 == Univ.AUContext.size auctx2) then
    error IncompatibleInstances
  else if not (UGraph.check_subtype (Environ.universes env) auctx2 auctx1) then
    error (IncompatibleConstraints auctx1)
  else
    Environ.push_context ~strict:false (Univ.AUContext.repr auctx2) env

(* for now we do not allow reorderings *)

let check_inductive cst env mp1 l info1 mp2 mib2 spec2 subst1 subst2 reso1 reso2= 
  let kn1 = KerName.make2 mp1 l in
  let kn2 = KerName.make2 mp2 l in
  let error why = error_signature_mismatch l spec2 why in
  let check_conv why cst poly f = check_conv_error error why cst poly f in
  let mib1 =
    match info1 with
      | IndType ((_,0), mib) -> Declareops.subst_mind_body subst1 mib
      | _ -> error (InductiveFieldExpected mib2)
  in
  let env, inst =
    match mib1.mind_universes, mib2.mind_universes with
    | Monomorphic_ind _, Monomorphic_ind _ -> env, Univ.Instance.empty
    | Polymorphic_ind auctx, Polymorphic_ind auctx' ->
      let env = check_polymorphic_instance error env auctx auctx' in
      env, Univ.make_abstract_instance auctx'
    | Cumulative_ind cumi, Cumulative_ind cumi' ->
      (** Currently there is no way to control variance of inductive types, but
          just in case we require that they are in a subtyping relation. *)
      let () =
        let v = ACumulativityInfo.variance cumi in
        let v' = ACumulativityInfo.variance cumi' in
        if not (Array.for_all2 Variance.check_subtype v' v) then
          CErrors.anomaly Pp.(str "Variance of " ++ KerName.print kn1 ++
            str " is not compatible with the one of " ++ KerName.print kn2)
      in
      let auctx = Univ.ACumulativityInfo.univ_context cumi in
      let auctx' = Univ.ACumulativityInfo.univ_context cumi' in
      let env = check_polymorphic_instance error env auctx auctx' in
      env, Univ.make_abstract_instance auctx'
    | _ -> error 
             (CumulativeStatusExpected (Declareops.inductive_is_cumulative mib2))
  in
  let mib2 =  Declareops.subst_mind_body subst2 mib2 in
  let check_inductive_type cst name t1 t2 =
    check_conv (NotConvertibleInductiveField name)
      cst (inductive_is_polymorphic mib1) infer_conv_leq env t1 t2
  in

  let check_packet cst p1 p2 =
    let check f test why = if not (test (f p1) (f p2)) then error why in
      check (fun p -> p.mind_consnames) (Array.equal Id.equal) NotSameConstructorNamesField;
      check (fun p -> p.mind_typename) Id.equal NotSameInductiveNameInBlockField;
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check (fun p -> p.mind_nrealargs) Int.equal (NotConvertibleInductiveField p2.mind_typename); (* How can it fail since the type of inductive are checked below? [HH] *)
      (* kelim ignored *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done because part of the inductive types *)
      (* Don't check the sort of the type if polymorphic *)
      let ty1 = type_of_inductive env ((mib1, p1), inst) in
      let ty2 = type_of_inductive env ((mib2, p2), inst) in
      let cst = check_inductive_type cst p2.mind_typename ty1 ty2 in
	cst
  in
  let mind = MutInd.make1 kn1 in
  let check_cons_types i cst p1 p2 =
    Array.fold_left3
      (fun cst id t1 t2 -> check_conv (NotConvertibleConstructorField id) cst
	(inductive_is_polymorphic mib1) infer_conv env t1 t2)
      cst
      p2.mind_consnames
      (arities_of_specif (mind, inst) (mib1, p1))
      (arities_of_specif (mind, inst) (mib2, p2))
  in
  let check f test why = if not (test (f mib1) (f mib2)) then error (why (f mib2)) in
  check (fun mib -> mib.mind_finite<>CoFinite) (==) (fun x -> FiniteInductiveFieldExpected x);
  check (fun mib -> mib.mind_ntypes) Int.equal (fun x -> InductiveNumbersFieldExpected x);
  assert (List.is_empty mib1.mind_hyps && List.is_empty mib2.mind_hyps);
  assert (Array.length mib1.mind_packets >= 1
	    && Array.length mib2.mind_packets >= 1);

  (* Check that the expected numbers of uniform parameters are the same *)
  (* No need to check the contexts of parameters: it is checked *)
  (* at the time of checking the inductive arities in check_packet. *)
  (* Notice that we don't expect the local definitions to match: only *)
  (* the inductive types and constructors types have to be convertible *)
  check (fun mib -> mib.mind_nparams) Int.equal (fun x -> InductiveParamsNumberField x);

  begin
    let kn2' = kn_of_delta reso2 kn2 in
    if KerName.equal kn2 kn2' ||
       MutInd.equal (mind_of_delta_kn reso1 kn1)
                    (subst_mind subst2 (MutInd.make kn2 kn2'))
    then ()
    else error NotEqualInductiveAliases
  end;
  (* we check that records and their field names are preserved. *)
  (** FIXME: this check looks nonsense *)
  check (fun mib -> mib.mind_record <> NotRecord) (==) (fun x -> RecordFieldExpected x);
  if mib1.mind_record <> NotRecord then begin
    let rec names_prod_letin t = match kind t with
      | Prod(n,_,t) -> n::(names_prod_letin t)
      | LetIn(n,_,_,t) -> n::(names_prod_letin t)
      | Cast(t,_,_) -> names_prod_letin t
      | _ -> []
    in
    assert (Int.equal (Array.length mib1.mind_packets) 1);
    assert (Int.equal (Array.length mib2.mind_packets) 1);
    assert (Int.equal (Array.length mib1.mind_packets.(0).mind_user_lc) 1);
    assert (Int.equal (Array.length mib2.mind_packets.(0).mind_user_lc) 1);
    check (fun mib ->
      let nparamdecls = List.length mib.mind_params_ctxt in
      let names = names_prod_letin (mib.mind_packets.(0).mind_user_lc.(0)) in
      snd (List.chop nparamdecls names)) (List.equal Name.equal)
      (fun x -> RecordProjectionsExpected x);
  end;
  (* we first check simple things *)
  let cst =
    Array.fold_left2 check_packet cst mib1.mind_packets mib2.mind_packets
  in
  (* and constructor types in the end *)
  let cst =
    Array.fold_left2_i check_cons_types cst mib1.mind_packets mib2.mind_packets
  in
    cst

    
let check_constant cst env l info1 cb2 spec2 subst1 subst2 =
  let error why = error_signature_mismatch l spec2 why in
  let check_conv cst poly f = check_conv_error error cst poly f in
  let check_type poly cst env t1 t2 =
    let err = NotConvertibleTypeField (env, t1, t2) in
    check_conv err cst poly infer_conv_leq env t1 t2
  in
  match info1 with
    | Constant cb1 ->
      let () = assert (List.is_empty cb1.const_hyps && List.is_empty cb2.const_hyps) in
      let cb1 = Declareops.subst_const_body subst1 cb1 in
      let cb2 = Declareops.subst_const_body subst2 cb2 in
      (* Start by checking universes *)
      let poly, env =
        match cb1.const_universes, cb2.const_universes with
        | Monomorphic_const _, Monomorphic_const _ ->
          false, env
        | Polymorphic_const auctx1, Polymorphic_const auctx2 ->
          true, check_polymorphic_instance error env auctx1 auctx2
        | Monomorphic_const _, Polymorphic_const _ ->
          error (PolymorphicStatusExpected true)
        | Polymorphic_const _, Monomorphic_const _ ->
          error (PolymorphicStatusExpected false)
      in
      (* Now check types *)
      let typ1 = cb1.const_type in
      let typ2 = cb2.const_type in
      let cst = check_type poly cst env typ1 typ2 in
      (* Now we check the bodies:
	 - A transparent constant can only be implemented by a compatible
	   transparent constant.
         - In the signature, an opaque is handled just as a parameter:
           anything of the right type can implement it, even if bodies differ.
      *)
      (match cb2.const_body with
	| Undef _ | OpaqueDef _ -> cst
	| Def lc2 ->
	  (match cb1.const_body with
	    | Undef _ | OpaqueDef _ -> error NotConvertibleBodyField
	    | Def lc1 ->
	      (* NB: cb1 might have been strengthened and appear as transparent.
		 Anyway [check_conv] will handle that afterwards. *)
	      let c1 = Mod_subst.force_constr lc1 in
	      let c2 = Mod_subst.force_constr lc2 in
	      check_conv NotConvertibleBodyField cst poly infer_conv env c1 c2))
   | IndType ((kn,i),mind1) ->
       CErrors.user_err Pp.(str @@
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by an inductive type. Hint: you can rename the " ^
       "inductive type and give a definition to map the old name to the new " ^
       "name.")
   | IndConstr (((kn,i),j),mind1) ->
      CErrors.user_err Pp.(str @@
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by a constructor. Hint: you can rename the " ^
       "constructor and give a definition to map the old name to the new " ^
       "name.")

let rec check_modules cst env msb1 msb2 subst1 subst2 =
  let mty1 = module_type_of_module msb1 in
  let mty2 =  module_type_of_module msb2 in
  check_modtypes cst env mty1 mty2 subst1 subst2 false

and check_signatures cst env mp1 sig1 mp2 sig2 subst1 subst2 reso1 reso2= 
  let map1 = make_labmap mp1 sig1 in
  let check_one_body cst (l,spec2) =
    match spec2 with
	| SFBconst cb2 ->
            check_constant cst env l (get_obj mp1 map1 l)
	      cb2 spec2 subst1 subst2
	| SFBmind mib2 ->
	    check_inductive cst env mp1 l (get_obj mp1 map1 l)
	      mp2 mib2 spec2 subst1 subst2 reso1 reso2
	| SFBmodule msb2 ->
	    begin match get_mod mp1 map1 l with
	      | Module msb -> check_modules cst env msb msb2 subst1 subst2
	      | _ -> error_signature_mismatch l spec2 ModuleFieldExpected
	    end
	| SFBmodtype mtb2 ->
	    let mtb1 = match get_mod mp1 map1 l with
	      | Modtype mtb -> mtb
	      | _ -> error_signature_mismatch l spec2 ModuleTypeFieldExpected
	    in
	    let env =
              add_module_type mtb2.mod_mp mtb2
	        (add_module_type mtb1.mod_mp mtb1 env)
            in
	    check_modtypes cst env mtb1 mtb2 subst1 subst2 true
  in
    List.fold_left check_one_body cst sig2

and check_modtypes cst env mtb1 mtb2 subst1 subst2 equiv =
  if mtb1==mtb2 || mtb1.mod_type == mtb2.mod_type then cst
  else
    let rec check_structure cst env str1 str2 equiv subst1 subst2 =
      match str1,str2 with
      |NoFunctor list1,
       NoFunctor list2 ->
	if equiv then
	  let subst2 = add_mp mtb2.mod_mp mtb1.mod_mp mtb1.mod_delta subst2 in
          let cst1 = check_signatures cst env
	    mtb1.mod_mp list1 mtb2.mod_mp list2 subst1 subst2
	    mtb1.mod_delta mtb2.mod_delta
          in
          let cst2 = check_signatures cst env
	    mtb2.mod_mp list2 mtb1.mod_mp list1 subst2 subst1
	    mtb2.mod_delta  mtb1.mod_delta
	  in
	  Univ.Constraint.union cst1 cst2
	else
	  check_signatures cst env
	    mtb1.mod_mp list1 mtb2.mod_mp list2 subst1 subst2
	    mtb1.mod_delta  mtb2.mod_delta
      |MoreFunctor (arg_id1,arg_t1,body_t1),
       MoreFunctor (arg_id2,arg_t2,body_t2) ->
        let mp2 = MPbound arg_id2 in
	let subst1 = join (map_mbid arg_id1 mp2 arg_t2.mod_delta) subst1 in
	let cst = check_modtypes cst env arg_t2 arg_t1 subst2 subst1 equiv in
        (* contravariant *)
	let env = add_module_type mp2 arg_t2 env in
	let env =
          if Modops.is_functor body_t1 then env
          else add_module
            {mod_mp = mtb1.mod_mp;
	     mod_expr = Abstract;
	     mod_type = subst_signature subst1 body_t1;
	     mod_type_alg = None;
	     mod_constraints = mtb1.mod_constraints;
	     mod_retroknowledge = ModBodyRK [];
	     mod_delta = mtb1.mod_delta} env
	in
	check_structure cst env body_t1 body_t2 equiv subst1 subst2
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
    in
    check_structure cst env mtb1.mod_type mtb2.mod_type equiv subst1 subst2

let check_subtypes env sup super =
  let env = add_module_type sup.mod_mp sup env in
  let env = Environ.push_context_set ~strict:true super.mod_constraints env in
  check_modtypes Univ.Constraint.empty env
    (strengthen sup sup.mod_mp) super empty_subst
    (map_mp super.mod_mp sup.mod_mp sup.mod_delta) false

