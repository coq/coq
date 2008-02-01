(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

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
  | Modtype of struct_expr_body

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
       add_nameobjects_of_mib (make_kn mp empty_dirpath l) mib map
    | SFBmodule mb -> add_map (Module mb)
    | SFBmodtype mtb -> add_map (Modtype mtb)
  in
    List.fold_right add_one list Labmap.empty

let check_conv_error error cst f env a1 a2 =
  try
    Constraint.union cst (f env a1 a2)
  with
      NotConvertible -> error ()

(* for now we do not allow reorderings *)
let check_inductive cst env msid1 l info1 mib2 spec2 = 
  let kn = make_kn (MPself msid1) empty_dirpath l in
  let error () = error_not_match l spec2 in
  let check_conv cst f = check_conv_error error cst f in
  let mib1 = 
    match info1 with
      | IndType ((_,0), mib) -> mib
      | _ -> error ()
  in
  let check_inductive_type cst env t1 t2 =

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
      | Type _, Type _ -> (* shortcut here *) mk_Prop, mk_Prop
      | (Prop _, Type _) | (Type _,Prop _) -> error ()
      | _ -> (s1, s2) in
    check_conv cst conv_leq env 
      (Sign.mkArity (ctx1,s1)) (Sign.mkArity (ctx2,s2))
  in

  let check_packet cst p1 p2 =
    let check f = if f p1 <> f p2 then error () in
      check (fun p -> p.mind_consnames);
      check (fun p -> p.mind_typename);
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check (fun p -> p.mind_nrealargs);
      (* kelim ignored *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done because part of the inductive types *)
      (* Don't check the sort of the type if polymorphic *)
      let cst = check_inductive_type cst env (type_of_inductive env (mib1,p1)) (type_of_inductive env (mib2,p2))
      in
	cst
  in
  let check_cons_types i cst p1 p2 =
    array_fold_left2 
      (fun cst t1 t2 -> check_conv cst conv env t1 t2)
      cst
      (arities_of_specif kn (mib1,p1))
      (arities_of_specif kn (mib2,p2))
  in
  let check f = if f mib1 <> f mib2 then error () in
  check (fun mib -> mib.mind_finite);
  check (fun mib -> mib.mind_ntypes);
  assert (mib1.mind_hyps=[] && mib2.mind_hyps=[]);
  assert (Array.length mib1.mind_packets >= 1 
	    && Array.length mib2.mind_packets >= 1);

  (* Check that the expected numbers of uniform parameters are the same *)
  (* No need to check the contexts of parameters: it is checked *)
  (* at the time of checking the inductive arities in check_packet. *)
  (* Notice that we don't expect the local definitions to match: only *)
  (* the inductive types and constructors types have to be convertible *)
  check (fun mib -> mib.mind_nparams);

  begin 
    match mib2.mind_equiv with
      | None -> ()
      | Some kn2' -> 
	  let kn2 = scrape_mind env kn2' in
	  let kn1 = match mib1.mind_equiv with
	      None -> kn
	    | Some kn1' -> scrape_mind env kn1'
	  in
	    if kn1 <> kn2 then error ()
  end;
  (* we check that records and their field names are preserved. *)
  check (fun mib -> mib.mind_record);
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
    check (fun mib -> names_prod_letin mib.mind_packets.(0).mind_user_lc.(0));
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
    
let check_constant cst env msid1 l info1 cb2 spec2 = 
  let error () = error_not_match l spec2 in
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
      if Sign.isArity t2 then
        let (ctx2,s2) = Sign.destArity t2 in
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
                Sign.mkArity (ctx1,mk_Prop), Sign.mkArity (ctx2,mk_Prop)
            | Prop _ ->
              (* The type in the interface is inferred, it may be the case
                 that the type in the implementation is smaller because
                 the body is more reduced. We safely collapse the upper
                 type to Prop *)
                Sign.mkArity (ctx1,mk_Prop), Sign.mkArity (ctx2,mk_Prop)
            | Type _ ->
              (* The type in the interface is inferred and the type in the
                 implementation is not inferred or is inferred but from a
                 more reduced body so that it is just a variable. Since
                 constraints of the form "univ <= max(...)" are not
                 expressible in the system of algebraic universes: we fail
                 (the user has to use an explicit type in the interface *)
                error ()
          with UserError _ (* "not an arity" *) ->
            error () end
        | _ -> t1,t2
      else
        (t1,t2) in
    check_conv cst conv_leq env t1 t2
  in

  match info1 with
   | Constant cb1 ->
      assert (cb1.const_hyps=[] && cb2.const_hyps=[]) ;
      (*Start by checking types*)
      let typ1 = Typeops.type_of_constant_type env cb1.const_type in
      let typ2 = Typeops.type_of_constant_type env cb2.const_type in
      let cst = check_type cst env typ1 typ2 in
      let con = make_con (MPself msid1) empty_dirpath l in
      let cst =
       match cb2.const_body with
         | None -> cst
         | Some lc2 ->
	     let c2 = Declarations.force lc2 in
	     let c1 = match cb1.const_body with
	       | Some lc1 -> Declarations.force lc1
	       | None -> mkConst con
	     in
	       check_conv cst conv env c1 c2
      in
       cst
   | IndType ((kn,i),mind1) ->
      ignore (Util.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by an inductive type. Hint: you can rename the " ^
       "inductive type and give a definition to map the old name to the new " ^
       "name."));
      assert (mind1.mind_hyps=[] && cb2.const_hyps=[]) ;
      if cb2.const_body <> None then error () ;
      let arity1 = type_of_inductive env (mind1,mind1.mind_packets.(i)) in
      let typ2 = Typeops.type_of_constant_type env cb2.const_type in
       check_conv cst conv_leq env arity1 typ2
   | IndConstr (((kn,i),j) as cstr,mind1) ->
      ignore (Util.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by a constructor. Hint: you can rename the " ^
       "constructor and give a definition to map the old name to the new " ^
       "name."));
      assert (mind1.mind_hyps=[] && cb2.const_hyps=[]) ;
      if cb2.const_body <> None then error () ;
      let ty1 = type_of_constructor cstr (mind1,mind1.mind_packets.(i)) in
      let ty2 = Typeops.type_of_constant_type env cb2.const_type in
       check_conv cst conv env ty1 ty2
   | _ -> error ()
	      
let rec check_modules cst env msid1 l msb1 msb2 =
  let mp = (MPdot(MPself msid1,l)) in
  let mty1 = strengthen env (type_of_mb env msb1) mp in
  let cst = check_modtypes cst env mty1 (type_of_mb env msb2) false in
    begin
    match msb1.mod_equiv, msb2.mod_equiv with
      | _, None -> ()
      | None, Some mp2 -> 
	  check_modpath_equiv env mp mp2
      | Some mp1, Some mp2 ->
	  check_modpath_equiv env mp1 mp2
  end;
  cst
	

and check_signatures cst env (msid1,sig1) (msid2,sig2') = 
  let mp1 = MPself msid1 in
  let env = add_signature mp1 sig1 env in 
  let sig2 = subst_signature_msid msid2 mp1 sig2' in
  let map1 = make_label_map mp1 sig1 in
  let check_one_body cst (l,spec2) = 
    let info1 = 
      try 
	Labmap.find l map1 
      with 
	  Not_found -> error_no_such_label_sub l (string_of_msid msid1) (string_of_msid msid2)
    in
      match spec2 with
	| SFBconst cb2 ->
	    check_constant cst env msid1 l info1 cb2 spec2
	| SFBmind mib2 -> 
	    check_inductive cst env msid1 l info1 mib2 spec2
	| SFBmodule msb2 -> 
	    let msb1 = 
	      match info1 with
		| Module msb -> msb
		| _ -> error_not_match l spec2
	    in
	      check_modules cst env msid1 l msb1 msb2
	| SFBmodtype mtb2 ->
	    let mtb1 = 
	      match info1 with
		| Modtype mtb -> mtb
		| _ -> error_not_match l spec2
	    in
	      check_modtypes cst env mtb1 mtb2 true
  in
    List.fold_left check_one_body cst sig2
    
and check_modtypes cst env mtb1 mtb2 equiv = 
  if mtb1==mtb2 then cst else (* just in case  :) *)
  let mtb1' = eval_struct env mtb1 in
  let mtb2' = eval_struct env mtb2 in
    if mtb1'==mtb2' then cst else
    match mtb1', mtb2' with
      | SEBstruct (msid1,list1), 
	SEBstruct (msid2,list2) -> 
	  let cst = check_signatures cst env (msid1,list1) (msid2,list2) in
	  if equiv then
	    check_signatures cst env (msid2,list2) (msid1,list1) 
	  else
	    cst
      | SEBfunctor (arg_id1,arg_t1,body_t1), 
	SEBfunctor (arg_id2,arg_t2,body_t2) ->
	  let cst = check_modtypes cst env arg_t2 arg_t1 equiv in 
	    (* contravariant *)
	  let env = 
	    add_module (MPbound arg_id2) (module_body_of_type arg_t2) env 
	  in
	  let body_t1' = 
            (* since we are just checking well-typedness we do not need
               to expand any constant. Hence the identity resolver. *)
	    subst_modtype 
              (map_mbid arg_id1 (MPbound arg_id2) None)
	      body_t1
	  in
	  check_modtypes cst env body_t1' body_t2 equiv
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
	  
let check_subtypes env sup super = 
  check_modtypes Constraint.empty env sup super false
