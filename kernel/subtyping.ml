(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Environ
open Reduction
open Inductive
open Modops
open Mod_subst
open Entries
(*i*)

(* This local type is used to subtype a constant with a constructor or
   an inductive type. It can also be useful to allow reorderings in
   inductive types *)
type namedobject =
  | Constant of constant_body
  | IndType of inductive * mutual_inductive_body
  | IndConstr of constructor * mutual_inductive_body
  | Module of module_body
  | Modtype of module_type_body

(* adds above information about one mutual inductive: all types and
   constructors *)

let add_nameobjects_of_mib ln mib map =
  let add_nameobjects_of_one j oib map =
    let ip = (ln,j) in
    let map =
      array_fold_right_i
      (fun i id map ->
        Labmap.add (label_of_id id) (IndConstr((ip,i+1), mib)) map)
      oib.mind_consnames
      map
    in
      Labmap.add (label_of_id oib.mind_typename) (IndType (ip, mib)) map
  in
    array_fold_right_i add_nameobjects_of_one mib.mind_packets map


(* creates namedobject map for the whole signature *)

let make_label_map mp list =
  let add_one (l,e) map =
   let add_map obj = Labmap.add l obj map in
   match e with
    | SFBconst cb -> add_map (Constant cb)
    | SFBmind mib ->
       add_nameobjects_of_mib (make_mind mp empty_dirpath l) mib map
    | SFBmodule mb -> add_map (Module mb)
    | SFBmodtype mtb -> add_map (Modtype mtb)
  in
    List.fold_right add_one list Labmap.empty

let check_conv_error error why cst f env a1 a2 =
  try
    union_constraints cst (f env a1 a2)
  with
      NotConvertible -> error why

(* for now we do not allow reorderings *)

let check_inductive cst env mp1 l info1 mp2 mib2 spec2 subst1 subst2 reso1 reso2= 
  let kn1 = make_mind mp1 empty_dirpath l in
  let kn2 = make_mind mp2 empty_dirpath l in
  let error why = error_signature_mismatch l spec2 why in
  let check_conv why cst f = check_conv_error error why cst f in
  let mib1 =
    match info1 with
      | IndType ((_,0), mib) -> subst_mind subst1 mib
      | _ -> error (InductiveFieldExpected mib2)
  in
  let mib2 =  subst_mind subst2 mib2 in
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
      cst conv_leq env (mkArity (ctx1,s1)) (mkArity (ctx2,s2))
  in

  let check_packet cst p1 p2 =
    let check f why = if f p1 <> f p2 then error why in
      check (fun p -> p.mind_consnames) NotSameConstructorNamesField;
      check (fun p -> p.mind_typename) NotSameInductiveNameInBlockField;
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check (fun p -> p.mind_nrealargs) (NotConvertibleInductiveField p2.mind_typename); (* How can it fail since the type of inductive are checked below? [HH] *)
      (* kelim ignored *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done because part of the inductive types *)
      (* Don't check the sort of the type if polymorphic *)
      let cst = check_inductive_type cst p2.mind_typename env (type_of_inductive env (mib1,p1)) (type_of_inductive env (mib2,p2))
      in
	cst
  in
  let check_cons_types i cst p1 p2 =
    array_fold_left3
      (fun cst id t1 t2 -> check_conv (NotConvertibleConstructorField id) cst conv env t1 t2)
      cst
      p2.mind_consnames
      (arities_of_specif kn1 (mib1,p1))
      (arities_of_specif kn1 (mib2,p2))
  in
  let check f why = if f mib1 <> f mib2 then error (why (f mib2)) in
  check (fun mib -> mib.mind_finite) (fun x -> FiniteInductiveFieldExpected x);
  check (fun mib -> mib.mind_ntypes) (fun x -> InductiveNumbersFieldExpected x);
  assert (mib1.mind_hyps=[] && mib2.mind_hyps=[]);
  assert (Array.length mib1.mind_packets >= 1
	    && Array.length mib2.mind_packets >= 1);

  (* Check that the expected numbers of uniform parameters are the same *)
  (* No need to check the contexts of parameters: it is checked *)
  (* at the time of checking the inductive arities in check_packet. *)
  (* Notice that we don't expect the local definitions to match: only *)
  (* the inductive types and constructors types have to be convertible *)
  check (fun mib -> mib.mind_nparams) (fun x -> InductiveParamsNumberField x);

  begin  
  match mind_of_delta reso2 kn2  with
      | kn2' when kn2=kn2' -> ()
      | kn2' -> 
	  if not (eq_mind (mind_of_delta reso1 kn1) (subst_ind subst2 kn2')) then 
	    error NotEqualInductiveAliases
  end;
  (* we check that records and their field names are preserved. *)
  check (fun mib -> mib.mind_record) (fun x -> RecordFieldExpected x);
  if mib1.mind_record then begin
    let rec names_prod_letin t = match kind_of_term t with
      | Prod(n,_,t) -> n::(names_prod_letin t)
      | LetIn(n,_,_,t) -> n::(names_prod_letin t)
      | Cast(t,_,_) -> names_prod_letin t
      | _ -> []
    in
    assert (Array.length mib1.mind_packets = 1);
    assert (Array.length mib2.mind_packets = 1);
    assert (Array.length mib1.mind_packets.(0).mind_user_lc = 1);
    assert (Array.length mib2.mind_packets.(0).mind_user_lc = 1);
    check (fun mib ->
      let nparamdecls = List.length mib.mind_params_ctxt in
      let names = names_prod_letin (mib.mind_packets.(0).mind_user_lc.(0)) in
      snd (list_chop nparamdecls names))
      (fun x -> RecordProjectionsExpected x);
  end;
  (* we first check simple things *)
  let cst =
    array_fold_left2 check_packet cst mib1.mind_packets mib2.mind_packets
  in
  (* and constructor types in the end *)
  let cst =
    array_fold_left2_i check_cons_types cst mib1.mind_packets mib2.mind_packets
  in
    cst

    
let check_constant cst env mp1 l info1 cb2 spec2 subst1 subst2 = 
  let error why = error_signature_mismatch l spec2 why in
  let check_conv cst f = check_conv_error error cst f in
  let check_type cst env t1 t2 =

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
            error NotConvertibleTypeField end
        | _ ->
	  t1,t2
      else
        (t1,t2) in
    check_conv NotConvertibleTypeField cst conv_leq env t1 t2
  in

  match info1 with
    | Constant cb1 ->
      assert (cb1.const_hyps=[] && cb2.const_hyps=[]) ;
      let cb1 = subst_const_body subst1 cb1 in
      let cb2 = subst_const_body subst2 cb2 in
      (* Start by checking types*)
      let typ1 = Typeops.type_of_constant_type env cb1.const_type in
      let typ2 = Typeops.type_of_constant_type env cb2.const_type in
      let cst = check_type cst env typ1 typ2 in
      (* Now we check the bodies *)
      (match cb2.const_body with
	| Undef _ -> cst
	| Def lc2 ->
	  (* Only a transparent cb1 can implement a transparent cb2.
	     NB: cb1 might have been strengthened and appear as transparent.
	     Anyway [check_conv] will handle that afterwards. *)
	  (match cb1.const_body with
	    | Undef _ | OpaqueDef _ -> error NotConvertibleBodyField
	    | Def lc1 ->
	      let c1 = Declarations.force lc1 in
	      let c2 = Declarations.force lc2 in
	      check_conv NotConvertibleBodyField cst conv env c1 c2)
	| OpaqueDef lc2 ->
	  (* Here cb1 can be either opaque or transparent. We need to
	     bypass the opacity and possibly do a delta step. *)
	  (match body_of_constant cb1 with
	    | None -> error NotConvertibleBodyField
	    | Some lc1 ->
	      let c1 = Declarations.force lc1 in
	      let c2 = Declarations.force_opaque lc2 in
	      let c1' = match (kind_of_term c1),(kind_of_term c2) with
		| Const n1,Const n2 when (eq_constant n1 n2) -> c1
		  (* cb1 may have been strengthened, we need to unfold it: *)
		| Const n1,_ ->
		  let cb1' = subst_const_body subst1 (lookup_constant n1 env)
		  in
		  (match cb1'.const_body with
		    | OpaqueDef lc1' -> Declarations.force_opaque lc1'
		    | _ -> c1)
		| _,_ -> c1
	      in
	      check_conv NotConvertibleBodyField cst conv env c1' c2))
   | IndType ((kn,i),mind1) ->
       ignore (Util.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by an inductive type. Hint: you can rename the " ^
       "inductive type and give a definition to map the old name to the new " ^
       "name."));
      assert (mind1.mind_hyps=[] && cb2.const_hyps=[]) ;
      if constant_has_body cb2 then error DefinitionFieldExpected;
      let arity1 = type_of_inductive env (mind1,mind1.mind_packets.(i)) in
      let typ2 = Typeops.type_of_constant_type env cb2.const_type in
       check_conv NotConvertibleTypeField cst conv_leq env arity1 typ2
   | IndConstr (((kn,i),j) as cstr,mind1) ->
      ignore (Util.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by a constructor. Hint: you can rename the " ^
       "constructor and give a definition to map the old name to the new " ^
       "name."));
      assert (mind1.mind_hyps=[] && cb2.const_hyps=[]) ;
      if constant_has_body cb2 then error DefinitionFieldExpected;
      let ty1 = type_of_constructor cstr (mind1,mind1.mind_packets.(i)) in
      let ty2 = Typeops.type_of_constant_type env cb2.const_type in
       check_conv NotConvertibleTypeField cst conv env ty1 ty2
   | _ -> error DefinitionFieldExpected

let rec check_modules cst env msb1 msb2 subst1 subst2 =
  let mty1 = module_type_of_module env None msb1 in
  let mty2 =  module_type_of_module env None msb2 in
  let cst = check_modtypes cst env mty1 mty2 subst1 subst2 false in
    cst

and check_signatures cst env mp1 sig1 mp2 sig2 subst1 subst2 reso1 reso2= 
  let map1 = make_label_map mp1 sig1 in
  let check_one_body cst (l,spec2) =
    let info1 =
      try
	Labmap.find l map1
      with
	  Not_found -> error_no_such_label_sub l
	    (string_of_mp mp1)
    in
      match spec2 with
	| SFBconst cb2 ->
	    check_constant cst env mp1 l info1 cb2 spec2 subst1 subst2
	| SFBmind mib2 ->
	    check_inductive cst env
	      mp1 l info1 mp2 mib2 spec2 subst1 subst2 reso1 reso2
	| SFBmodule msb2 ->
	    begin
	      match info1 with
		| Module msb -> check_modules cst env msb msb2 
		    subst1 subst2
		| _ -> error_signature_mismatch l spec2 ModuleFieldExpected
	    end
	| SFBmodtype mtb2 ->
	    let mtb1 =
	      match info1 with
		| Modtype mtb -> mtb
		| _ -> error_signature_mismatch l spec2 ModuleTypeFieldExpected
	    in
	    let env = add_module (module_body_of_type mtb2.typ_mp mtb2)
	      (add_module (module_body_of_type mtb1.typ_mp mtb1) env) in
	      check_modtypes cst env mtb1 mtb2 subst1 subst2 true
  in
    List.fold_left check_one_body cst sig2

and check_modtypes cst env mtb1 mtb2 subst1 subst2 equiv = 
  if mtb1==mtb2 then cst else 
  let mtb1',mtb2'=mtb1.typ_expr,mtb2.typ_expr in
  let rec check_structure cst env str1 str2 equiv subst1 subst2 = 
	match str1,str2 with
	  | SEBstruct (list1), 
	    SEBstruct (list2) -> 
	      if equiv then
		let subst2 = 
		  add_mp mtb2.typ_mp mtb1.typ_mp mtb1.typ_delta subst2 in
		Univ.union_constraints 
		  (check_signatures cst env
		     mtb1.typ_mp list1 mtb2.typ_mp list2 subst1 subst2
		  mtb1.typ_delta mtb2.typ_delta) 
		  (check_signatures cst env 
		     mtb2.typ_mp list2 mtb1.typ_mp list1 subst2 subst1
		  mtb2.typ_delta  mtb1.typ_delta)
	      else
		check_signatures cst env
		  mtb1.typ_mp list1 mtb2.typ_mp list2 subst1 subst2
		  mtb1.typ_delta  mtb2.typ_delta
	  | SEBfunctor (arg_id1,arg_t1,body_t1),
	      SEBfunctor (arg_id2,arg_t2,body_t2) ->
	      let subst1 = 
		(join (map_mbid arg_id1 (MPbound arg_id2) arg_t2.typ_delta) subst1) in
	      let cst = check_modtypes cst env 
		arg_t2 arg_t1 subst2 subst1
		equiv in 
		(* contravariant *)
	      let env = add_module 
		(module_body_of_type (MPbound arg_id2) arg_t2) env 
	      in
	      let env = match body_t1 with
		  SEBstruct str -> 
		    add_module {mod_mp = mtb1.typ_mp;
				mod_expr = None;
				mod_type = subst_struct_expr subst1 body_t1;
				mod_type_alg= None;
				mod_constraints=mtb1.typ_constraints;
				mod_retroknowledge = [];
				mod_delta = mtb1.typ_delta} env
		| _ -> env
	      in
		check_structure cst env body_t1 body_t2 equiv 
		  subst1
		  subst2
	  | _ , _ -> error_incompatible_modtypes mtb1 mtb2
      in
     if mtb1'== mtb2' then cst
     else check_structure cst env mtb1' mtb2' equiv subst1 subst2

let check_subtypes env sup super =
  let env = add_module 
		(module_body_of_type sup.typ_mp sup) env in
  check_modtypes empty_constraint env 
    (strengthen env sup sup.typ_mp) super empty_subst 
    (map_mp super.typ_mp sup.typ_mp sup.typ_delta) false

