(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module checks subtyping of module types *)

(*i*)
open Util
open Names
open Univ
open Term
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
  with Not_found -> error_no_such_label_sub l (string_of_mp mp)

let get_mod mp map l =
  try Label.Map.find l map.mods
  with Not_found -> error_no_such_label_sub l (string_of_mp mp)

let make_labmap mp list =
  let add_one (l,e) map =
   match e with
    | SFBconst cb -> { map with objs = Label.Map.add l (Constant cb) map.objs }
    | SFBmind mib -> { map with objs = add_mib_nameobjects mp l mib map.objs }
    | SFBmodule mb -> { map with mods = Label.Map.add l (Module mb) map.mods }
    | SFBmodtype mtb -> { map with mods = Label.Map.add l (Modtype mtb) map.mods }
  in
  List.fold_right add_one list empty_labmap


let check_conv_error error why cst poly u f env a1 a2 =
  try 
    let a1 = Vars.subst_instance_constr u a1 in
    let a2 = Vars.subst_instance_constr u a2 in
    let cst' = f env (Environ.universes env) a1 a2 in
      if poly then 
	if Constraint.is_empty cst' then cst
	else error (IncompatiblePolymorphism (env, a1, a2))
      else Constraint.union cst cst'
  with NotConvertible -> error why

(* for now we do not allow reorderings *)

let check_inductive cst env mp1 l info1 mp2 mib2 spec2 subst1 subst2 reso1 reso2= 
  let kn1 = KerName.make2 mp1 l in
  let kn2 = KerName.make2 mp2 l in
  let error why = error_signature_mismatch l spec2 why in
  let check_conv why cst poly u f = check_conv_error error why cst poly u f in
  let mib1 =
    match info1 with
      | IndType ((_,0), mib) -> Declareops.subst_mind_body subst1 mib
      | _ -> error (InductiveFieldExpected mib2)
  in
  let poly = 
    if not (mib1.mind_polymorphic == mib2.mind_polymorphic) then
      error (PolymorphicStatusExpected mib2.mind_polymorphic)
    else mib2.mind_polymorphic
  in
  let u = 
    if poly then 
      Errors.error ("Checking of subtyping of polymorphic" ^
		       " inductive types not implemented")
    else Instance.empty
  in
  let mib2 =  Declareops.subst_mind_body subst2 mib2 in
  let check_inductive_type cst name env t1 t2 =

    (* Due to sort-polymorphism in inductive types, the conclusions of
       t1 and t2, if in Type, are generated as the least upper bounds
       of the types of the constructors.

       By monotonicity of the infered l.u.b.  wrt subtyping (i.e.  if X:U
       |- T(X):s and |- M:U' and U'<=U then infer_type(T(M))<=s), each
       universe in the conclusion of t1 has an bounding universe in
       the conclusion of t2, so that we don't need to check the
       subtyping of the conclusions of t1 and t2.

       Even if we'd like to recheck it, the inference of constraints
       is not designed to deal with algebraic constraints of the form
       max-univ(u1..un) <= max-univ(u'1..u'n), so that it is not easy
       to recheck it (in short, we would need the actual graph of
       constraints as input while type checking is currently designed
       to output a set of constraints instead) *)

    (* So we cheat and replace the subtyping problem on algebraic
       constraints of the form max-univ(u1..un) <= max-univ(u'1..u'n)
       (that we know are necessary true) by trivial constraints that
       the constraint generator knows how to deal with *)

    let (ctx1,s1) = dest_arity env t1 in
    let (ctx2,s2) = dest_arity env t2 in
    let s1,s2 =
      match s1, s2 with
      | Type _, Type _ -> (* shortcut here *) prop_sort, prop_sort
      | (Prop _, Type _) | (Type _,Prop _) ->
	error (NotConvertibleInductiveField name)
      | _ -> (s1, s2) in
    check_conv (NotConvertibleInductiveField name)
      cst poly u infer_conv_leq env (mkArity (ctx1,s1)) (mkArity (ctx2,s2))
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
      let ty1, cst1 = constrained_type_of_inductive env ((mib1,p1),u) in
      let ty2, cst2 = constrained_type_of_inductive env ((mib2,p2),u) in
      let cst = Constraint.union cst1 (Constraint.union cst2 cst) in
      let cst = check_inductive_type cst p2.mind_typename env ty1 ty2 in
	cst
  in
  let mind = mind_of_kn kn1 in
  let check_cons_types i cst p1 p2 =
    Array.fold_left3
      (fun cst id t1 t2 -> check_conv (NotConvertibleConstructorField id) cst
	poly u infer_conv env t1 t2)
      cst
      p2.mind_consnames
      (arities_of_specif (mind,u) (mib1,p1))
      (arities_of_specif (mind,u) (mib2,p2))
  in
  let check f test why = if not (test (f mib1) (f mib2)) then error (why (f mib2)) in
  check (fun mib -> mib.mind_finite<>Decl_kinds.CoFinite) (==) (fun x -> FiniteInductiveFieldExpected x);
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
  check (fun mib -> mib.mind_record <> None) (==) (fun x -> RecordFieldExpected x);
  if mib1.mind_record <> None then begin
    let rec names_prod_letin t = match kind_of_term t with
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

    
let check_constant cst env mp1 l info1 cb2 spec2 subst1 subst2 = 
  let error why = error_signature_mismatch l spec2 why in
  let check_conv cst poly u f = check_conv_error error cst poly u f in
  let check_type poly u cst env t1 t2 =

    let err = NotConvertibleTypeField (env, t1, t2) in

    (* If the type of a constant is generated, it may mention
       non-variable algebraic universes that the general conversion
       algorithm is not ready to handle. Anyway, generated types of
       constants are functions of the body of the constant. If the
       bodies are the same in environments that are subtypes one of
       the other, the types are subtypes too (i.e. if Gamma <= Gamma',
       Gamma |- A |> T, Gamma |- A' |> T' and Gamma |- A=A' then T <= T').
       Hence they don't have to be checked again *)

    let t1,t2 =
      if isArity t2 then
        let (ctx2,s2) = destArity t2 in
        match s2 with
        | Type v when not (is_univ_variable v) ->
          (* The type in the interface is inferred and is made of algebraic
             universes *)
          begin try
            let (ctx1,s1) = dest_arity env t1 in
            match s1 with
            | Type u when not (is_univ_variable u) ->
              (* Both types are inferred, no need to recheck them. We
                 cheat and collapse the types to Prop *)
                mkArity (ctx1,prop_sort), mkArity (ctx2,prop_sort)
            | Prop _ ->
              (* The type in the interface is inferred, it may be the case
                 that the type in the implementation is smaller because
                 the body is more reduced. We safely collapse the upper
                 type to Prop *)
                mkArity (ctx1,prop_sort), mkArity (ctx2,prop_sort)
            | Type _ ->
              (* The type in the interface is inferred and the type in the
                 implementation is not inferred or is inferred but from a
                 more reduced body so that it is just a variable. Since
                 constraints of the form "univ <= max(...)" are not
                 expressible in the system of algebraic universes: we fail
                 (the user has to use an explicit type in the interface *)
                error NoTypeConstraintExpected
          with NotArity ->
            error err end
        | _ ->
	  t1,t2
      else
        (t1,t2) in
      check_conv err cst poly u infer_conv_leq env t1 t2
  in
  match info1 with
    | Constant cb1 ->
      let () = assert (List.is_empty cb1.const_hyps && List.is_empty cb2.const_hyps) in
      let cb1 = Declareops.subst_const_body subst1 cb1 in
      let cb2 = Declareops.subst_const_body subst2 cb2 in
      (* Start by checking universes *)
      let poly = 
	if not (cb1.const_polymorphic == cb2.const_polymorphic) then
	  error (PolymorphicStatusExpected cb2.const_polymorphic)
	else cb2.const_polymorphic
      in
      let cst', env', u = 
	if poly then 
	  let ctx1 = Univ.instantiate_univ_context cb1.const_universes in
	  let ctx2 = Univ.instantiate_univ_context cb2.const_universes in
	  let inst1, ctx1 = Univ.UContext.dest ctx1 in
	  let inst2, ctx2 = Univ.UContext.dest ctx2 in
	    if not (Univ.Instance.length inst1 == Univ.Instance.length inst2) then
	      error IncompatibleInstances
	    else 
	      let cstrs = Univ.enforce_eq_instances inst1 inst2 cst in
	      let cstrs = Univ.Constraint.union cstrs ctx2 in
		try 
		  (* The environment with the expected universes plus equality 
		     of the body instances with the expected instance *)
		  let env = Environ.add_constraints cstrs env in
		    (* Check that the given definition does not add any constraint over
		       the expected ones, so that it can be used in place of the original. *)
		    if Univ.check_constraints ctx1 (Environ.universes env) then
		      cstrs, env, inst2
		    else error (IncompatibleConstraints ctx1)
		with Univ.UniverseInconsistency incon -> 
		  error (IncompatibleUniverses incon)
	else cst, env, Univ.Instance.empty
      in
      (* Now check types *)
      let typ1 = Typeops.type_of_constant_type env' cb1.const_type in
      let typ2 = Typeops.type_of_constant_type env' cb2.const_type in
      let cst = check_type poly u cst env' typ1 typ2 in
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
	      check_conv NotConvertibleBodyField cst poly u infer_conv env' c1 c2))
   | IndType ((kn,i),mind1) ->
       ignore (Errors.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by an inductive type. Hint: you can rename the " ^
       "inductive type and give a definition to map the old name to the new " ^
       "name."));
      let () = assert (List.is_empty mind1.mind_hyps && List.is_empty cb2.const_hyps) in
      if Declareops.constant_has_body cb2 then error DefinitionFieldExpected;
      let u1 = inductive_instance mind1 in
      let arity1,cst1 = constrained_type_of_inductive env 
	((mind1,mind1.mind_packets.(i)),u1) in
      let cst2 =
        Declareops.constraints_of_constant (Environ.opaque_tables env) cb2 in 
      let typ2 = Typeops.type_of_constant_type env cb2.const_type in
      let cst = Constraint.union cst (Constraint.union cst1 cst2) in
      let error = NotConvertibleTypeField (env, arity1, typ2) in
       check_conv error cst false Univ.Instance.empty infer_conv_leq env arity1 typ2
   | IndConstr (((kn,i),j) as cstr,mind1) ->
      ignore (Errors.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by a constructor. Hint: you can rename the " ^
       "constructor and give a definition to map the old name to the new " ^
       "name."));
      let () = assert (List.is_empty mind1.mind_hyps && List.is_empty cb2.const_hyps) in
      if Declareops.constant_has_body cb2 then error DefinitionFieldExpected;
      let u1 = inductive_instance mind1 in
      let ty1,cst1 = constrained_type_of_constructor (cstr,u1) (mind1,mind1.mind_packets.(i)) in
      let cst2 =
        Declareops.constraints_of_constant (Environ.opaque_tables env) cb2 in
      let ty2 = Typeops.type_of_constant_type env cb2.const_type in
      let cst = Constraint.union cst (Constraint.union cst1 cst2) in
      let error = NotConvertibleTypeField (env, ty1, ty2) in
       check_conv error cst false Univ.Instance.empty infer_conv env ty1 ty2

let rec check_modules cst env msb1 msb2 subst1 subst2 =
  let mty1 = module_type_of_module msb1 in
  let mty2 =  module_type_of_module msb2 in
  check_modtypes cst env mty1 mty2 subst1 subst2 false

and check_signatures cst env mp1 sig1 mp2 sig2 subst1 subst2 reso1 reso2= 
  let map1 = make_labmap mp1 sig1 in
  let check_one_body cst (l,spec2) =
    match spec2 with
	| SFBconst cb2 ->
	    check_constant cst env mp1 l (get_obj mp1 map1 l)
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
	     mod_retroknowledge = [];
	     mod_delta = mtb1.mod_delta} env
	in
	check_structure cst env body_t1 body_t2 equiv subst1 subst2
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
    in
    check_structure cst env mtb1.mod_type mtb2.mod_type equiv subst1 subst2

let check_subtypes env sup super =
  let env = add_module_type sup.mod_mp sup env in
  check_modtypes Univ.Constraint.empty env
    (strengthen sup sup.mod_mp) super empty_subst
    (map_mp super.mod_mp sup.mod_mp sup.mod_delta) false

