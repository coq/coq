(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Errors
open Util
open Names
open Cic
open Term
open Declarations
open Environ
open Reduction
open Inductive
open Modops
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
  with Not_found -> error_no_such_label_sub l mp

let get_mod mp map l =
  try Label.Map.find l map.mods
  with Not_found -> error_no_such_label_sub l mp

let make_labmap mp list =
  let add_one (l,e) map =
   match e with
    | SFBconst cb -> { map with objs = Label.Map.add l (Constant cb) map.objs }
    | SFBmind mib -> { map with objs = add_mib_nameobjects mp l mib map.objs }
    | SFBmodule mb -> { map with mods = Label.Map.add l (Module mb) map.mods }
    | SFBmodtype mtb -> { map with mods = Label.Map.add l (Modtype mtb) map.mods }
  in
  List.fold_right add_one list empty_labmap


let check_conv_error error f env a1 a2 =
  try
    f env a1 a2
  with
      NotConvertible -> error ()

(* for now we do not allow reorderings *)
let check_inductive  env mp1 l info1 mib2 spec2 subst1 subst2= 
  let kn = MutInd.make2 mp1 l in
  let error () = error_not_match l spec2 in
  let check_conv f = check_conv_error error f in
  let mib1 =
    match info1 with
      | IndType ((_,0), mib) -> mib
      | _ -> error ()
  in
  let mib2 = subst_mind subst2 mib2 in
  let check eq f = if not (eq (f mib1) (f mib2)) then error () in
  let bool_equal (x : bool) (y : bool) = x = y in
  let u = 
    check bool_equal (fun x -> x.mind_polymorphic);
    if mib1.mind_polymorphic then (
      check Univ.Instance.equal (fun x -> Univ.UContext.instance x.mind_universes);
      Univ.UContext.instance mib1.mind_universes)
    else Univ.Instance.empty
  in
  let eq_projection_body p1 p2 =
    let check eq f = if not (eq (f p1) (f p2)) then error () in
    check eq_mind (fun x -> x.proj_ind);
    check (==) (fun x -> x.proj_npars);
    check (==) (fun x -> x.proj_arg);
    check (eq_constr) (fun x -> x.proj_type);
    check (eq_constr) (fun x -> fst x.proj_eta);
    check (eq_constr) (fun x -> snd x.proj_eta);
    check (eq_constr) (fun x -> x.proj_body); true
  in
  let check_inductive_type env t1 t2 =

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
      | Type _, Type _ -> (* shortcut here *) Prop Null, Prop Null
      | (Prop _, Type _) | (Type _,Prop _) -> error ()
      | _ -> (s1, s2) in
    check_conv conv_leq env
      (mkArity (ctx1,s1)) (mkArity (ctx2,s2))
  in

  let check_packet p1 p2 =
    let check eq f = if not (eq (f p1) (f p2)) then error () in
    check
      (fun a1 a2 -> Array.equal Id.equal a1 a2)
      (fun p -> p.mind_consnames);
      check Id.equal (fun p -> p.mind_typename);
      (* nf_lc later *)
      (* nf_arity later *)
      (* user_lc ignored *)
      (* user_arity ignored *)
      check Int.equal (fun p -> p.mind_nrealargs);
      (* kelim ignored *)
      (* listrec ignored *)
      (* finite done *)
      (* nparams done *)
      (* params_ctxt done because part of the inductive types *)
      (* Don't check the sort of the type if polymorphic *)
      check_inductive_type env
        (type_of_inductive env ((mib1,p1),u)) (type_of_inductive env ((mib2,p2),u))
  in
  let check_cons_types i p1 p2 =
    Array.iter2 (check_conv conv env)
      (arities_of_specif (kn,u) (mib1,p1))
      (arities_of_specif (kn,u) (mib2,p2))
  in
  check (==) (fun mib -> mib.mind_finite);
  check Int.equal (fun mib -> mib.mind_ntypes);
  assert (Array.length mib1.mind_packets >= 1
	    && Array.length mib2.mind_packets >= 1);

  (* Check that the expected numbers of uniform parameters are the same *)
  (* No need to check the contexts of parameters: it is checked *)
  (* at the time of checking the inductive arities in check_packet. *)
  (* Notice that we don't expect the local definitions to match: only *)
  (* the inductive types and constructors types have to be convertible *)
  check Int.equal (fun mib -> mib.mind_nparams);

  (*begin
    match mib2.mind_equiv with
      | None -> ()
      | Some kn2' ->
	  let kn2 = scrape_mind env kn2' in
	  let kn1 = match mib1.mind_equiv with
	      None -> kn
	    | Some kn1' -> scrape_mind env kn1'
	  in
	    if kn1 <> kn2 then error ()
  end;*)
  (* we check that records and their field names are preserved. *)
  let record_equal x y =
    match x, y with
    | None, None -> true
    | Some None, Some None -> true
    | Some (Some (id1,p1,pb1)), Some (Some (id2,p2,pb2)) ->
      Id.equal id1 id2 &&
      Array.for_all2 eq_con_chk p1 p2 &&
      Array.for_all2 eq_projection_body pb1 pb2
    | _, _ -> false
  in
  check record_equal (fun mib -> mib.mind_record);
  if mib1.mind_record != None then begin
    let rec names_prod_letin t = match t with
      | Prod(n,_,t) -> n::(names_prod_letin t)
      | LetIn(n,_,_,t) -> n::(names_prod_letin t)
      | Cast(t,_,_) -> names_prod_letin t
      | _ -> []
    in
    assert (Array.length mib1.mind_packets = 1);
    assert (Array.length mib2.mind_packets = 1);
    assert (Array.length mib1.mind_packets.(0).mind_user_lc = 1);
    assert (Array.length mib2.mind_packets.(0).mind_user_lc = 1);
    check
      (fun l1 l2 -> List.equal Name.equal l1 l2)
      (fun mib -> names_prod_letin mib.mind_packets.(0).mind_user_lc.(0));
  end;
  (* we first check simple things *)
  Array.iter2 check_packet mib1.mind_packets mib2.mind_packets;
  (* and constructor types in the end *)
  let _ = Array.map2_i check_cons_types mib1.mind_packets mib2.mind_packets
  in ()

let check_constant env mp1 l info1 cb2 spec2 subst1 subst2 =
  let error () = error_not_match l spec2 in
  let check_conv f = check_conv_error error f in
  let check_type env t1 t2 =

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
        | Type v when not (Univ.is_univ_variable v) ->
          (* The type in the interface is inferred and is made of algebraic
             universes *)
          begin try
            let (ctx1,s1) = dest_arity env t1 in
            match s1 with
            | Type u when not (Univ.is_univ_variable u) ->
              (* Both types are inferred, no need to recheck them. We
                 cheat and collapse the types to Prop *)
                mkArity (ctx1,Prop Null), mkArity (ctx2,Prop Null)
            | Prop _ ->
              (* The type in the interface is inferred, it may be the case
                 that the type in the implementation is smaller because
                 the body is more reduced. We safely collapse the upper
                 type to Prop *)
                mkArity (ctx1,Prop Null), mkArity (ctx2,Prop Null)
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
    check_conv conv_leq env t1 t2
  in
    match info1 with
      | Constant cb1 ->
	let cb1 = subst_const_body subst1 cb1 in
	let cb2 = subst_const_body subst2 cb2 in
	(*Start by checking types*)
	let typ1 = Typeops.type_of_constant_type env cb1.const_type in
	let typ2 = Typeops.type_of_constant_type env cb2.const_type in
	check_type env typ1 typ2;
	(* Now we check the bodies:
	 - A transparent constant can only be implemented by a compatible
	   transparent constant.
         - In the signature, an opaque is handled just as a parameter:
           anything of the right type can implement it, even if bodies differ.
	*)
	(match cb2.const_body with
	  | Undef _ | OpaqueDef _ -> ()
	  | Def lc2 ->
	    (match cb1.const_body with
	      | Undef _ | OpaqueDef _ -> error ()
	      | Def lc1 ->
	        (* NB: cb1 might have been strengthened and appear as transparent.
	           Anyway [check_conv] will handle that afterwards. *)
		let c1 = force_constr lc1 in
		let c2 = force_constr lc2 in
		check_conv conv env c1 c2))
      | IndType ((kn,i),mind1) ->
	  ignore (Errors.error (
		    "The kernel does not recognize yet that a parameter can be " ^
		      "instantiated by an inductive type. Hint: you can rename the " ^
		      "inductive type and give a definition to map the old name to the new " ^
		      "name."));
      if constant_has_body cb2 then error () ;
      let u = inductive_instance mind1 in
      let arity1 = type_of_inductive env ((mind1,mind1.mind_packets.(i)),u) in
      let typ2 = Typeops.type_of_constant_type env cb2.const_type in
       check_conv conv_leq env arity1 typ2
   | IndConstr (((kn,i),j) as cstr,mind1) ->
      ignore (Errors.error (
       "The kernel does not recognize yet that a parameter can be " ^
       "instantiated by a constructor. Hint: you can rename the " ^
       "constructor and give a definition to map the old name to the new " ^
       "name."));
      if constant_has_body cb2 then error () ;
      let u1 = inductive_instance mind1 in
      let ty1 = type_of_constructor (cstr,u1) (mind1,mind1.mind_packets.(i)) in
      let ty2 = Typeops.type_of_constant_type env cb2.const_type in
       check_conv conv env ty1 ty2

let rec check_modules  env msb1 msb2 subst1 subst2 =
  let mty1 = module_type_of_module None msb1 in
  let mty2 = module_type_of_module None msb2 in
    check_modtypes env mty1 mty2 subst1 subst2 false;
 

and check_signatures env mp1 sig1 sig2 subst1 subst2 = 
  let map1 = make_labmap mp1 sig1 in
  let check_one_body  (l,spec2) =
      match spec2 with
	| SFBconst cb2 ->
	    check_constant  env mp1 l (get_obj mp1 map1 l)
	      cb2 spec2 subst1 subst2
	| SFBmind mib2 ->
	    check_inductive env mp1 l (get_obj mp1 map1 l)
	      mib2 spec2 subst1 subst2
	| SFBmodule msb2 ->
	    begin
	      match get_mod mp1 map1 l with
		| Module msb -> check_modules env msb msb2 
		    subst1 subst2
		| _ -> error_not_match l spec2
	    end
	| SFBmodtype mtb2 ->
	    let mtb1 =
	      match get_mod mp1 map1 l with
		| Modtype mtb -> mtb
		| _ -> error_not_match l spec2
	    in
	    let env =
              add_module_type mtb2.mod_mp mtb2
	        (add_module_type mtb1.mod_mp mtb1 env)
            in
	    check_modtypes env mtb1 mtb2 subst1 subst2 true
  in
  List.iter check_one_body sig2

and check_modtypes env mtb1 mtb2 subst1 subst2 equiv =
  if mtb1==mtb2 || mtb1.mod_type == mtb2.mod_type then ()
  else
    let rec check_structure  env str1 str2 equiv subst1 subst2 =
      match str1,str2 with
      | NoFunctor (list1),
        NoFunctor (list2) ->
	  check_signatures env mtb1.mod_mp list1 list2 subst1 subst2;
	  if equiv then
	    check_signatures env mtb2.mod_mp list2 list1 subst1 subst2
	  else
	    ()
      | MoreFunctor (arg_id1,arg_t1,body_t1),
	MoreFunctor (arg_id2,arg_t2,body_t2) ->
	  check_modtypes env
	    arg_t2 arg_t1
	    (map_mp arg_t1.mod_mp arg_t2.mod_mp) subst2
	    equiv;
	  (* contravariant *)
	  let env = add_module_type (MPbound arg_id2) arg_t2 env in
	  let env =
            if is_functor body_t1 then env
            else
	      let env = shallow_remove_module mtb1.mod_mp env in
	      add_module {mod_mp = mtb1.mod_mp;
			  mod_expr = Abstract;
			  mod_type = body_t1;
			  mod_type_alg = None;
			  mod_constraints = mtb1.mod_constraints;
			  mod_retroknowledge = [];
			  mod_delta = mtb1.mod_delta} env
	  in
	  check_structure env body_t1 body_t2 equiv
	    (join (map_mbid arg_id1 (MPbound arg_id2)) subst1)
	    subst2
      | _ , _ -> error_incompatible_modtypes mtb1 mtb2
    in
    check_structure env mtb1.mod_type mtb2.mod_type equiv subst1 subst2

let check_subtypes env sup super =
  check_modtypes env (strengthen sup sup.mod_mp) super empty_subst
      (map_mp super.mod_mp sup.mod_mp) false
