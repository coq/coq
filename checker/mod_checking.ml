
open Pp
open Util
open Names
open Term
open Inductive
open Reduction
open Typeops
open Indtypes
open Modops
open Subtyping
open Declarations
open Environ

(************************************************************************)
(* Checking constants *)

let refresh_arity ar =
  let ctxt, hd = decompose_prod_assum ar in
  match hd with
      Sort (Type u) when not (Univ.is_univ_variable u) ->
        let u' = Univ.fresh_local_univ() in
        mkArity (ctxt,Type u'),
        Univ.enforce_geq u' u Univ.Constraint.empty
    | _ -> ar, Univ.Constraint.empty

let check_constant_declaration env kn cb =
  Flags.if_verbose msgnl (str "  checking cst: " ++ prcon kn);
(*  let env = add_constraints cb.const_constraints env in*)
  let env' = check_named_ctxt env cb.const_hyps in
  (match cb.const_type with
      NonPolymorphicType ty ->
        let ty, cu = refresh_arity ty in
        let envty = add_constraints cu env' in 
        let _ = infer_type envty ty in
        (match cb.const_body with
          | Some bd ->
              let j = infer env' (force_constr bd) in
              conv_leq envty j ty
          | None -> ())
    | PolymorphicArity(ctxt,par) ->
        let _ = check_ctxt env ctxt in
        check_polymorphic_arity env ctxt par);
  add_constant kn cb env

(************************************************************************)
(* Checking modules *)


exception Not_path

let path_of_mexpr = function
  | SEBident mp -> mp
  | _ -> raise Not_path

let rec list_split_assoc k rev_before = function
  | [] -> raise Not_found
  | (k',b)::after when k=k' -> rev_before,b,after
  | h::tail -> list_split_assoc k (h::rev_before) tail

let rec list_fold_map2 f e = function 
  |  []  -> (e,[],[])
  |  h::t -> 
       let e',h1',h2' = f e h in
       let e'',t1',t2' = list_fold_map2 f e' t in
	 e'',h1'::t1',h2'::t2'


let check_alias (s1:substitution) s2 =
  if s1 <> s2 then failwith "Incorrect alias"

let check_definition_sub env cb1 cb2 =
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
                raise Reduction.NotConvertible
          with UserError _ (* "not an arity" *) ->
            raise Reduction.NotConvertible end
        | _ -> t1,t2
      else
        (t1,t2) in
    Reduction.conv_leq env t1 t2
  in
  assert (cb1.const_hyps=[] && cb2.const_hyps=[]) ;
  (*Start by checking types*)
  let typ1 = Typeops.type_of_constant_type env cb1.const_type in
  let typ2 = Typeops.type_of_constant_type env cb2.const_type in
  check_type env typ1 typ2;
  (match cb2 with
    | {const_body=Some lc2;const_opaque=false} ->
	let c2 = force_constr lc2 in
	let c1 = match cb1.const_body with
	  | Some lc1 -> force_constr lc1
	  | None -> assert false in
	Reduction.conv env c1 c2
    | _ -> ())

let lookup_modtype mp env =
  try Environ.lookup_modtype mp env
  with Not_found ->
    failwith ("Unknown module type: "^string_of_mp mp)


let rec check_with env mtb with_decl = 
  match with_decl with
    | With_definition_body _ -> 
	check_with_aux_def env mtb with_decl;
	empty_subst
    | With_module_body _ -> 
	check_with_aux_mod env mtb with_decl

and check_with_aux_def env mtb with_decl = 
  let msid,sig_b = match (eval_struct env mtb) with 
    | SEBstruct(msid,sig_b) ->
	msid,sig_b
    | _ -> error_signature_expected mtb
  in
  let id,idl = match with_decl with 
    | With_definition_body (id::idl,_) | With_module_body (id::idl,_,_,_) ->
                                           id,idl
    | With_definition_body ([],_) | With_module_body ([],_,_,_) -> assert false
  in
  let l = label_of_id id in
    try
      let rev_before,spec,after = list_split_assoc l [] sig_b in
      let before = List.rev rev_before in
      let env' = Modops.add_signature (MPself msid) before env in
	match with_decl with
          | With_definition_body ([],_) -> assert false
	  | With_definition_body ([id],c) -> 
	      let cb = match spec with
		  SFBconst cb -> cb
		| _ -> error_not_a_constant l
	      in 
              check_definition_sub env' c cb
	  | With_definition_body (_::_,_) ->
	      let old = match spec with
		  SFBmodule msb -> msb
		| _ -> error_not_a_module l
	      in
		begin
		  match old.mod_expr with
                    | None ->
			let new_with_decl = match with_decl with
			    With_definition_body (_,c) ->
                              With_definition_body (idl,c)
			  | With_module_body (_,c,t,cst) ->
                              With_module_body (idl,c,t,cst) in 
			  check_with_aux_def env' (type_of_mb env old) new_with_decl
                    | Some msb ->
			error_a_generative_module_expected l
		end
	  | _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l

and check_with_aux_mod env mtb with_decl = 
  let initmsid,msid,sig_b =
    match eval_struct env mtb with 
    | SEBstruct(msid,sig_b) ->
        let msid'=(refresh_msid msid) in
	msid,msid',(subst_signature_msid msid (MPself(msid')) sig_b)
    | _ -> error_signature_expected mtb in
  let id,idl = match with_decl with 
    | With_definition_body (id::idl,_) | With_module_body (id::idl,_,_,_) ->
        id,idl
    | With_definition_body ([],_) | With_module_body ([],_,_,_) -> assert false
  in
  let l = label_of_id id in
    try
      let rev_before,spec,after = list_split_assoc l [] sig_b in
      let before = List.rev rev_before in
      let rec mp_rec = function
	| [] -> MPself initmsid
	| i::r -> MPdot(mp_rec r,label_of_id i)
      in 
      let env' = Modops.add_signature (MPself msid) before env in
	match with_decl with
          | With_module_body ([],_,_,_) -> assert false
	  | With_module_body ([id], mp,_,_) ->
	      let old,alias = match spec with
		  SFBmodule msb -> Some msb,None
		| SFBalias (mp',_,_) -> None,Some mp'
		| _ -> error_not_a_module l
	      in
	      let mtb' = lookup_modtype mp env' in
	      let _ =
		match old,alias with
		    Some msb,None -> ()
		  | None,Some mp' ->
		      check_modpath_equiv env' mp mp'
		  | _,_ ->
		      anomaly "Mod_typing:no implementation and no alias"
	      in
		join (map_mp (mp_rec [id]) mp) mtb'.typ_alias
        | With_module_body (_::_,mp,_,_) -> 
	    let old = match spec with
		SFBmodule msb -> msb
	      | _ -> error_not_a_module l
	    in
	      begin
		match old.mod_expr with
                    None ->
                      let new_with_decl = match with_decl with
			  With_definition_body (_,c) -> 
			    With_definition_body (idl,c)
			| With_module_body (_,c,t,cst) ->
                            With_module_body (idl,c,t,cst) in
		      let sub =
			check_with_aux_mod env' 
			  (type_of_mb env old) new_with_decl in
		      join (map_mp (mp_rec idl) mp) sub
                  | Some msb ->
                      error_a_generative_module_expected l
              end
	| _ -> anomaly "Modtyping:incorrect use of with"
    with
	Not_found -> error_no_such_label l
      | Reduction.NotConvertible -> error_with_incorrect l

and check_module_type env mty =
  if mty.typ_strength <> None then
    failwith "strengthening of module types not supported";
  let sub = check_modexpr env mty.typ_expr in
  check_alias mty.typ_alias sub

and check_module env mb =
  let sub =
    match mb.mod_expr, mb.mod_type with
      | None, None -> 
	  anomaly "Mod_typing.translate_module: empty type and expr in module entry"
      | None, Some mtb -> check_modexpr env mtb

      | Some mexpr, _ -> 
	  let sub1 = check_modexpr env mexpr in
	  (match mb.mod_type with
	    | None ->  sub1
	    | Some mte -> 
		let sub2 = check_modexpr env mte in
                check_subtypes env
		  {typ_expr = mexpr;
		   typ_strength = None;
		   typ_alias = sub1;}
		  {typ_expr = mte;
		   typ_strength = None;
		   typ_alias = sub2;};
		sub2) in
  check_alias mb.mod_alias sub

and check_structure_field (s,env) mp lab = function
  | SFBconst cb ->
      let c = make_con mp empty_dirpath lab in
      (s,check_constant_declaration env c cb)
  | SFBmind mib ->
      let kn = make_kn mp empty_dirpath lab in
      (s,Indtypes.check_inductive env kn mib)
  | SFBmodule msb ->
      check_module env msb;
      let mp1 = MPdot(mp,lab) in
      let is_fun, sub = Modops.update_subst env msb mp1 in
      ((if is_fun then s else join s sub),
       Modops.add_module (MPdot(mp,lab)) msb env)
  | SFBalias(mp2,_,cst) ->
      (* cf Safe_typing.add_alias *)
      (try
        let mp' = MPdot(mp,lab) in
        let mp2' = scrape_alias mp2 env in
        let _,sub = Modops.update_subst env (lookup_module mp2' env) mp2' in
        let sub = update_subst sub (map_mp mp' mp2') in
        let sub = join_alias sub (map_mp mp' mp2') in
        let sub = add_mp mp' mp2' sub in
        (join s sub, register_alias mp' mp2 env)
      with Not_found -> failwith "unkown aliased module")
  | SFBmodtype mty ->
      let kn = MPdot(mp, lab) in
      check_module_type env mty;
      (join s mty.typ_alias, add_modtype kn mty env)

and check_modexpr env mse = match mse with
  | SEBident mp ->
      let mp = scrape_alias mp env in
      let mtb = lookup_modtype mp env in
      mtb.typ_alias
  | SEBfunctor (arg_id, mtb, body) ->
      check_module_type env mtb;
      let env' = add_module (MPbound arg_id) (module_body_of_type mtb) env in
      let sub = check_modexpr env' body in
      sub
  | SEBapply (f,m,cst) ->
      let sub1 = check_modexpr env f in
      let f'= eval_struct env f in
      let farg_id, farg_b, fbody_b = destr_functor env f' in
      let mp =
	try scrape_alias (path_of_mexpr m) env
	with Not_path -> error_application_to_not_path m
	      (* place for nondep_supertype *) in
      let mtb = lookup_modtype mp env in
      check_subtypes env mtb farg_b;
      let sub2 = match eval_struct env m with
	| SEBstruct (msid,sign) -> 
	    join_alias 
	      (subst_key (map_msid msid mp) mtb.typ_alias)
	      (map_msid msid mp)
	| _ -> mtb.typ_alias in
      let sub3 = join_alias sub1 (map_mbid farg_id mp) in
      let sub4 = update_subst sub2 sub3 in
      join sub3 sub4
  | SEBwith(mte, with_decl) ->
	let sub1 = check_modexpr env mte in
	let sub2 = check_with env mte with_decl in
	join sub1 sub2
  | SEBstruct(msid,msb) ->
      let mp = MPself msid in
      let (sub,_) =
        List.fold_left (fun env (lab,mb) ->
          check_structure_field env mp lab mb) (empty_subst,env) msb in
      sub

(*
let rec add_struct_expr_constraints env = function
  | SEBident _ -> env

  | SEBfunctor (_,mtb,meb) -> 
      add_struct_expr_constraints 
	(add_modtype_constraints env mtb) meb

  | SEBstruct (_,structure_body) ->
      List.fold_left 
        (fun env (l,item) -> add_struct_elem_constraints env item)
        env
        structure_body

  | SEBapply (meb1,meb2,cst) ->
(*  let g = Univ.merge_constraints cst Univ.initial_universes in
msgnl(str"ADDING FUNCTOR APPLICATION CONSTRAINTS:"++fnl()++
      Univ.pr_universes g++str"============="++fnl());      
*)
      Environ.add_constraints cst 
        (add_struct_expr_constraints 
	  (add_struct_expr_constraints env meb1) 
	  meb2)
  | SEBwith(meb,With_definition_body(_,cb))->
      Environ.add_constraints cb.const_constraints
	(add_struct_expr_constraints env meb)
  | SEBwith(meb,With_module_body(_,_,cst))->
      Environ.add_constraints cst
	(add_struct_expr_constraints env meb)	
		
and add_struct_elem_constraints env = function 
  | SFBconst cb -> Environ.add_constraints cb.const_constraints env
  | SFBmind mib -> Environ.add_constraints mib.mind_constraints env
  | SFBmodule mb -> add_module_constraints env mb
  | SFBalias (mp,Some cst) -> Environ.add_constraints cst env
  | SFBalias (mp,None) -> env
  | SFBmodtype mtb -> add_modtype_constraints env mtb

and add_module_constraints env mb = 
  let env = match mb.mod_expr with
    | None -> env
    | Some meb -> add_struct_expr_constraints env meb
  in
  let env = match mb.mod_type with
    | None -> env
    | Some mtb -> 
	add_struct_expr_constraints env mtb
  in
    Environ.add_constraints mb.mod_constraints env

and add_modtype_constraints env mtb = 
  add_struct_expr_constraints env mtb.typ_expr
*)
