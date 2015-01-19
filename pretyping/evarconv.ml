(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Term
open Vars
open Closure
open Reduction
open Reductionops
open Termops
open Environ
open Recordops
open Evarutil
open Evarsolve
open Globnames
open Evd
open Pretype_errors

type unify_fun = transparent_state ->
  env -> evar_map -> conv_pb -> constr -> constr -> Evarsolve.unification_result

let debug_unification = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; Goptions.optdepr = false;
  Goptions.optname =
    "Print states sent to Evarconv unification";
  Goptions.optkey = ["Debug";"Unification"];
  Goptions.optread = (fun () -> !debug_unification);
  Goptions.optwrite = (fun a -> debug_unification:=a);
}

let unfold_projection env evd ts p c =
  let cst = Projection.constant p in
    if is_transparent_constant ts cst then
      let c' = Some (mkProj (Projection.make cst true, c)) in
	match ReductionBehaviour.get (Globnames.ConstRef cst) with
	| None -> c'
	| Some (recargs, nargs, flags) ->
	  if (List.mem `ReductionNeverUnfold flags) then None
	  else c'
    else None
      
let eval_flexible_term ts env evd c =
  match kind_of_term c with
  | Const (c,u as cu) ->
      if is_transparent_constant ts c
      then constant_opt_value_in env cu
      else None
  | Rel n ->
      (try let (_,v,_) = lookup_rel n env in Option.map (lift n) v
      with Not_found -> None)
  | Var id ->
      (try
	 if is_transparent_variable ts id then
	   let (_,v,_) = lookup_named id env in v
	 else None
       with Not_found -> None)
  | LetIn (_,b,_,c) -> Some (subst1 b c)
  | Lambda _ -> Some c
  | Proj (p, c) -> 
    if Projection.unfolded p then assert false
    else unfold_projection env evd ts p c
  | _ -> assert false

type flex_kind_of_term =
  | Rigid
  | MaybeFlexible of Constr.t (* reducible but not necessarily reduced *)
  | Flexible of existential

let flex_kind_of_term ts env evd c sk =
  match kind_of_term c with
    | LetIn _ | Rel _ | Const _ | Var _ | Proj _ ->
      Option.cata (fun x -> MaybeFlexible x) Rigid (eval_flexible_term ts env evd c)
    | Lambda _ when not (Option.is_empty (Stack.decomp sk)) -> MaybeFlexible c
    | Evar ev -> Flexible ev
    | Lambda _ | Prod _ | Sort _ | Ind _ | Construct _ | CoFix _ -> Rigid
    | Meta _ -> Rigid
    | Fix _ -> Rigid (* happens when the fixpoint is partially applied *)
    | Cast _ | App _ | Case _ -> assert false

let apprec_nohdbeta ts env evd c =
  let (t,sk as appr) = Reductionops.whd_nored_state evd (c, []) in
  if Stack.not_purely_applicative sk
  then Stack.zip (fst (whd_betaiota_deltazeta_for_iota_state
		   ts env evd Cst_stack.empty appr))
  else c

let position_problem l2r = function
  | CONV -> None
  | CUMUL -> Some l2r

let occur_rigidly ev evd t = 
  let (l, app) = decompose_app_vect t in 
  let rec aux t = 
    match kind_of_term (whd_evar evd t) with
    | App (f, c) -> if aux f then Array.exists aux c else false
    | Construct _ | Ind _ | Sort _ | Meta _ | Fix _ | CoFix _ -> true
    | Proj (p, c) -> not (aux c)
    | Evar (ev',_) -> if Evar.equal ev ev' then raise Occur else false
    | Cast (p, _, _) -> aux p
    | Lambda _ | LetIn _ -> false
    | Const _ -> false
    | Prod (_, b, t) -> ignore(aux b || aux t); true
    | Rel _ | Var _ -> false
    | Case _ -> false
  in Array.exists (fun t -> try ignore(aux t); false with Occur -> true) app

(* [check_conv_record env sigma (t1,stack1) (t2,stack2)] tries to decompose 
   the problem (t1 stack1) = (t2 stack2) into a problem

     stack1 = params1@[c1]@extra_args1
     stack2 = us2@extra_args2
     t1 params1 c1 = proji params (c xs)
     t2 us2 = head us
     extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (head us), for which we know that the i-th projection proji
   satisfies

      proji params (c xs) = head us

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record env sigma (t1,sk1) (t2,sk2) =
  let (proji, u), arg = Universes.global_app_of_constr t1 in
  let canon_s,sk2_effective =
    try
      match kind_of_term t2 with
	Prod (_,a,b) -> (* assert (l2=[]); *)
      	  if dependent (mkRel 1) b then raise Not_found
	  else lookup_canonical_conversion (proji, Prod_cs),
	    (Stack.append_app [|a;pop b|] Stack.empty)
      | Sort s ->
	lookup_canonical_conversion
	  (proji, Sort_cs (family_of_sort s)),[]
      | _ ->
	let c2 = global_of_constr t2 in
	  lookup_canonical_conversion (proji, Const_cs c2),sk2
    with Not_found ->
      let (c, cs) = lookup_canonical_conversion (proji,Default_cs) in 
	(c,cs),[]
  in
  let t', { o_DEF = c; o_CTX = ctx; o_INJ=n; o_TABS = bs;
        o_TPARAMS = params; o_NPARAMS = nparams; o_TCOMPS = us } = canon_s in
  let params1, c1, extra_args1 =
    match arg with
    | Some c -> (* A primitive projection applied to c *)
      let ty = Retyping.get_type_of ~lax:true env sigma c in
      let (i,u), ind_args = 
	try Inductiveops.find_mrectype env sigma ty 
	with _ -> raise Not_found
      in Stack.append_app_list ind_args Stack.empty, c, sk1
    | None ->
      match Stack.strip_n_app nparams sk1 with
      | Some (params1, c1, extra_args1) -> params1, c1, extra_args1
      | _ -> raise Not_found in
  let us2,extra_args2 =
    let l_us = List.length us in
      if Int.equal l_us 0 then Stack.empty,sk2_effective
      else match (Stack.strip_n_app (l_us-1) sk2_effective) with
      | None -> raise Not_found
      | Some (l',el,s') -> (l'@Stack.append_app [|el|] Stack.empty,s') in
  let subst, ctx' = Universes.fresh_universe_context_set_instance ctx in
  let c' = subst_univs_level_constr subst c in
  let t' = subst_univs_level_constr subst t' in
  let bs' = List.map (subst_univs_level_constr subst) bs in
  let h, _ = decompose_app_vect t' in
    ctx',(h, t2),c',bs',(Stack.append_app_list params Stack.empty,params1),
    (Stack.append_app_list us Stack.empty,us2),(extra_args1,extra_args2),c1,
    (n,Stack.zip(t2,sk2))

(* Precondition: one of the terms of the pb is an uninstantiated evar,
 * possibly applied to arguments. *)

let rec ise_try evd = function
    [] -> assert false
  | [f] -> f evd
  | f1::l ->
      match f1 evd with
      | Success _ as x -> x
      | UnifFailure _ -> ise_try evd l

let ise_and evd l =
  let rec ise_and i = function
      [] -> assert false
    | [f] -> f i
    | f1::l ->
        match f1 i with
	| Success i' -> ise_and i' l
	| UnifFailure _ as x -> x in
  ise_and evd l

(* This function requires to get the outermost arguments first.  It is
   a fold_right for backward compatibility.

   It tries to unify the suffix of 2 lists element by element and if
   it reaches the end of a list, it returns the remaining elements in
   the other list if there are some.
*)
let ise_exact ise x1 x2 =
  match ise x1 x2 with
  | None, out -> out
  | _, (UnifFailure _ as out) -> out
  | Some _, Success i -> UnifFailure (i,NotSameArgSize)

let ise_array2 evd f v1 v2 =
  let rec allrec i = function
    | -1 -> Success i
    | n ->
        match f i v1.(n) v2.(n) with
	| Success i' -> allrec i' (n-1)
	| UnifFailure _ as x -> x in
  let lv1 = Array.length v1 in
  if Int.equal lv1 (Array.length v2) then allrec evd (pred lv1)
  else UnifFailure (evd,NotSameArgSize)

(* Applicative node of stack are read from the outermost to the innermost
   but are unified the other way. *)
let rec ise_app_stack2 env f evd sk1 sk2 =
  match sk1,sk2 with
  | Stack.App node1 :: q1, Stack.App node2 :: q2 ->
     let (t1,l1) = Stack.decomp_node_last node1 q1 in
     let (t2,l2) = Stack.decomp_node_last node2 q2 in
     begin match ise_app_stack2 env f evd l1 l2 with
	   |(_,UnifFailure _) as x -> x
	   |x,Success i' -> x,f env i' CONV t1 t2
     end
  | _, _ -> (sk1,sk2), Success evd

(* This function tries to unify 2 stacks element by element. It works
   from the end to the beginning. If it unifies a non empty suffix of
   stacks but not the entire stacks, the first part of the answer is
   Some(the remaining prefixes to tackle)) *)
let ise_stack2 no_app env evd f sk1 sk2 =
  let rec ise_stack2 deep i sk1 sk2 =
    let fail x = if deep then Some (List.rev sk1, List.rev sk2), Success i
      else None, x in
    match sk1, sk2 with
    | [], [] -> None, Success i
    | Stack.Case (_,t1,c1,_)::q1, Stack.Case (_,t2,c2,_)::q2 ->
      (match f env i CONV t1 t2 with
      | Success i' ->
	(match ise_array2 i' (fun ii -> f env ii CONV) c1 c2 with
	| Success i'' -> ise_stack2 true i'' q1 q2
        | UnifFailure _ as x -> fail x)
      | UnifFailure _ as x -> fail x)
    | Stack.Proj (n1,a1,p1,_)::q1, Stack.Proj (n2,a2,p2,_)::q2 ->
       if eq_constant (Projection.constant p1) (Projection.constant p2)
       then ise_stack2 true i q1 q2
       else fail (UnifFailure (i, NotSameHead))
    | Stack.Fix (((li1, i1),(_,tys1,bds1 as recdef1)),a1,_)::q1,
      Stack.Fix (((li2, i2),(_,tys2,bds2)),a2,_)::q2 ->
      if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
        match ise_and i [
	  (fun i -> ise_array2 i (fun ii -> f env ii CONV) tys1 tys2);
	  (fun i -> ise_array2 i (fun ii -> f (push_rec_types recdef1 env) ii CONV) bds1 bds2);
	  (fun i -> ise_exact (ise_stack2 false i) a1 a2)] with
        | Success i' -> ise_stack2 true i' q1 q2
        | UnifFailure _ as x -> fail x
      else fail (UnifFailure (i,NotSameHead))
    | Stack.Update _ :: _, _ | Stack.Shift _ :: _, _
    | _, Stack.Update _ :: _ | _, Stack.Shift _ :: _ -> assert false
    | Stack.App _ :: _, Stack.App _ :: _ ->
       if no_app && deep then fail ((*dummy*)UnifFailure(i,NotSameHead)) else
	 begin match ise_app_stack2 env f i sk1 sk2 with
	       |_,(UnifFailure _ as x) -> fail x
	       |(l1, l2), Success i' -> ise_stack2 true i' l1 l2
	 end
    |_, _ -> fail (UnifFailure (i,(* Maybe improve: *) NotSameHead))
  in ise_stack2 false evd (List.rev sk1) (List.rev sk2)

(* Make sure that the matching suffix is the all stack *)
let exact_ise_stack2 env evd f sk1 sk2 =
  let rec ise_stack2 i sk1 sk2 =
    match sk1, sk2 with
    | [], [] -> Success i
    | Stack.Case (_,t1,c1,_)::q1, Stack.Case (_,t2,c2,_)::q2 ->
      ise_and i [
      (fun i -> ise_stack2 i q1 q2);
      (fun i -> ise_array2 i (fun ii -> f env ii CONV) c1 c2);
      (fun i -> f env i CONV t1 t2)]
    | Stack.Fix (((li1, i1),(_,tys1,bds1 as recdef1)),a1,_)::q1,
      Stack.Fix (((li2, i2),(_,tys2,bds2)),a2,_)::q2 ->
      if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
	ise_and i [
	  (fun i -> ise_stack2 i q1 q2);
	  (fun i -> ise_array2 i (fun ii -> f env ii CONV) tys1 tys2);
	  (fun i -> ise_array2 i (fun ii -> f (push_rec_types recdef1 env) ii CONV) bds1 bds2);
	  (fun i -> ise_stack2 i a1 a2)]
      else UnifFailure (i,NotSameHead)
    | Stack.Proj (n1,a1,p1,_)::q1, Stack.Proj (n2,a2,p2,_)::q2 ->
       if eq_constant (Projection.constant p1) (Projection.constant p2)
       then ise_stack2 i q1 q2
       else (UnifFailure (i, NotSameHead))
    | Stack.Update _ :: _, _ | Stack.Shift _ :: _, _
    | _, Stack.Update _ :: _ | _, Stack.Shift _ :: _ -> assert false
    | Stack.App _ :: _, Stack.App _ :: _ ->
	 begin match ise_app_stack2 env f i sk1 sk2 with
	       |_,(UnifFailure _ as x) -> x
	       |(l1, l2), Success i' -> ise_stack2 i' l1 l2
	 end
    |_, _ -> UnifFailure (i,(* Maybe improve: *) NotSameHead)
  in
  if Reductionops.Stack.compare_shape sk1 sk2 then
    ise_stack2 evd (List.rev sk1) (List.rev sk2)
  else UnifFailure (evd, (* Dummy *) NotSameHead)
    
let rec evar_conv_x ts env evd pbty term1 term2 =
  let term1 = whd_head_evar evd term1 in
  let term2 = whd_head_evar evd term2 in
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]
     could have found, we do it only if the terms are free of evar.
     Note: incomplete heuristic... *)
  let ground_test =
    if is_ground_term evd term1 && is_ground_term evd term2 then (
      let evd, b = 
	try infer_conv ~pb:pbty ~ts:(fst ts) env evd term1 term2 
	with Univ.UniverseInconsistency _ -> evd, false
      in
	if b then Some (evd, true)
	else if is_ground_env evd env then Some (evd, false)
	else None)
    else None
  in
  match ground_test with
    | Some (evd, true) -> Success evd
    | Some (evd, false) -> UnifFailure (evd,ConversionFailed (env,term1,term2))
    | None ->
	(* Until pattern-unification is used consistently, use nohdbeta to not
	   destroy beta-redexes that can be used for 1st-order unification *)
        let term1 = apprec_nohdbeta (fst ts) env evd term1 in
        let term2 = apprec_nohdbeta (fst ts) env evd term2 in
	let default () = 
          evar_eqappr_x ts env evd pbty
            (whd_nored_state evd (term1,Stack.empty), Cst_stack.empty)
            (whd_nored_state evd (term2,Stack.empty), Cst_stack.empty)
	in
          begin match kind_of_term term1, kind_of_term term2 with
          | Evar ev, _ when Evd.is_undefined evd (fst ev) ->
            (match solve_simple_eqn (evar_conv_x ts) env evd
              (position_problem true pbty,ev,term2) with
	      | UnifFailure (_,OccurCheck _) -> 
		(* Eta-expansion might apply *) default ()
	      | x -> x)
          | _, Evar ev when Evd.is_undefined evd (fst ev) ->
            (match solve_simple_eqn (evar_conv_x ts) env evd
              (position_problem false pbty,ev,term1) with
	      | UnifFailure (_, OccurCheck _) ->
		(* Eta-expansion might apply *) default () 
	      | x -> x)
          | _ -> default ()
        end

and evar_eqappr_x ?(rhs_is_already_stuck = false) ts env evd pbty
    ((term1,sk1 as appr1),csts1) ((term2,sk2 as appr2),csts2) =
  let default_fail i = (* costly *)
    UnifFailure (i,ConversionFailed (env, Stack.zip appr1, Stack.zip appr2)) in
  let quick_fail i = (* not costly, loses info *)
    UnifFailure (i, NotSameHead)
  in
  let miller_pfenning on_left fallback ev lF tM evd =
    match is_unification_pattern_evar env evd ev lF tM with
      | None -> fallback ()
      | Some l1' -> (* Miller-Pfenning's patterns unification *)
	let t2 = nf_evar evd tM in
	let t2 = solve_pattern_eqn env l1' t2 in
	  solve_simple_eqn (evar_conv_x ts) env evd
	    (position_problem on_left pbty,ev,t2) 
  in
  let consume_stack on_left (termF,skF) (termO,skO) evd =
    let switch f a b = if on_left then f a b else f b a in
    let not_only_app = Stack.not_purely_applicative skO in
    match switch (ise_stack2 not_only_app env evd (evar_conv_x ts)) skF skO with
      |Some (l,r), Success i' when on_left && (not_only_app || List.is_empty l) ->
	switch (evar_conv_x ts env i' pbty) (Stack.zip(termF,l)) (Stack.zip(termO,r))
      |Some (r,l), Success i' when not on_left && (not_only_app || List.is_empty l) ->
	switch (evar_conv_x ts env i' pbty) (Stack.zip(termF,l)) (Stack.zip(termO,r))
      |None, Success i' -> switch (evar_conv_x ts env i' pbty) termF termO
      |_, (UnifFailure _ as x) -> x
      |Some _, _ -> UnifFailure (evd,NotSameArgSize) in
  let eta env evd onleft sk term sk' term' =
    assert (match sk with [] -> true | _ -> false);
    let (na,c1,c'1) = destLambda term in
    let c = nf_evar evd c1 in
    let env' = push_rel (na,None,c) env in
    let out1 = whd_betaiota_deltazeta_for_iota_state
      (fst ts) env' evd Cst_stack.empty (c'1, Stack.empty) in
    let out2 = whd_nored_state evd
      (Stack.zip (term', sk' @ [Stack.Shift 1]), Stack.append_app [|mkRel 1|] Stack.empty), 
      Cst_stack.empty in
    if onleft then evar_eqappr_x ts env' evd CONV out1 out2
    else evar_eqappr_x ts env' evd CONV out2 out1
  in
  let rigids env evd sk term sk' term' =
    let b,univs = Universes.eq_constr_universes term term' in
      if b then
       ise_and evd [(fun i ->
         let cstrs = Universes.to_constraints (Evd.universes i) univs in
           try Success (Evd.add_constraints i cstrs)
           with Univ.UniverseInconsistency p -> UnifFailure (i, UnifUnivInconsistency p));
                  (fun i -> exact_ise_stack2 env i (evar_conv_x ts) sk sk')]
      else UnifFailure (evd,NotSameHead)
  in
  let flex_maybeflex on_left ev ((termF,skF as apprF),cstsF) ((termM, skM as apprM),cstsM) vM =
    let switch f a b = if on_left then f a b else f b a in
    let not_only_app = Stack.not_purely_applicative skM in
    let f1 i =
      match Stack.list_of_app_stack skF with
      | None -> default_fail evd
      | Some lF -> 
        let tM = Stack.zip apprM in
	  miller_pfenning on_left
	    (fun () -> if not_only_app then (* Postpone the use of an heuristic *)
	      switch (fun x y -> Success (add_conv_pb (pbty,env,x,y) i)) (Stack.zip apprF) tM
	    else quick_fail i)
	  ev lF tM i
    and consume (termF,skF as apprF) (termM,skM as apprM) i = 
      if not (Stack.is_empty skF && Stack.is_empty skM) then
        consume_stack on_left apprF apprM i
      else quick_fail i
    and delta i =
      switch (evar_eqappr_x ts env i pbty) (apprF,cstsF)
	(whd_betaiota_deltazeta_for_iota_state (fst ts) env i cstsM (vM,skM))
    in    
    let default i = ise_try i [f1; consume apprF apprM; delta]
    in
      match kind_of_term termM with
      | Proj (p, c) when not (Stack.is_empty skF) ->
	(* Might be ?X args = p.c args', and we have to eta-expand the 
	   primitive projection if |args| >= |args'|+1. *)
	let nargsF = Stack.args_size skF and nargsM = Stack.args_size skM in
	  begin
	    (* ?X argsF' ~= (p.c ..) argsM' -> ?X ~= (p.c ..), no need to expand *)
	    if nargsF <= nargsM then default evd
	    else 
	      let f =
		try 
		  let termM' = Retyping.expand_projection env evd p c [] in
		  let apprM', cstsM' = 
		    whd_betaiota_deltazeta_for_iota_state (fst ts) env evd cstsM (termM',skM)
		  in
		  let delta' i = 
		    switch (evar_eqappr_x ts env i pbty) (apprF,cstsF) (apprM',cstsM') 
		  in
		    fun i -> ise_try i [f1; consume apprF apprM'; delta']
		with Retyping.RetypeError _ ->
		(* Happens thanks to w_unify building ill-typed terms *) 
		  default
	      in f evd
	  end
      | _ -> default evd
  in
  let flex_rigid on_left ev (termF, skF as apprF) (termR, skR as apprR) =
    let switch f a b = if on_left then f a b else f b a in
    let eta evd =
             match kind_of_term termR with
	     | Lambda _ -> eta env evd false skR termR skF termF
	     | Construct u -> eta_constructor ts env evd skR u skF termF
	     | _ -> UnifFailure (evd,NotSameHead)
    in
    match Stack.list_of_app_stack skF with
    | None ->
        ise_try evd [consume_stack on_left apprF apprR; eta]
    | Some lF ->
        let tR = Stack.zip apprR in
	  miller_pfenning on_left
	    (fun () ->
	      ise_try evd 
	        [eta;(* Postpone the use of an heuristic *)
		 (fun i -> 
		   if not (occur_rigidly (fst ev) i tR) then
                     let i,tF =
                       if isRel tR || isVar tR then
                         (* Optimization so as to generate candidates *)
                         let i,ev = evar_absorb_arguments env i ev lF in
                         i,mkEvar ev
                       else
                         i,Stack.zip apprF in
		     switch (fun x y -> Success (add_conv_pb (pbty,env,x,y) i))
	               tF tR
		   else
                     UnifFailure (evd,OccurCheck (fst ev,tR)))])
	    ev lF tR evd
  in
  let app_empty = match sk1, sk2 with [], [] -> true | _ -> false in
  (* Evar must be undefined since we have flushed evars *)
  let () = if !debug_unification then
	     let open Pp in
	     pp (v 0 (pr_state appr1 ++ cut () ++ pr_state appr2 ++ cut ()) 
		 ++ fnl ()) in
  match (flex_kind_of_term (fst ts) env evd term1 sk1, 
	 flex_kind_of_term (fst ts) env evd term2 sk2) with
    | Flexible (sp1,al1 as ev1), Flexible (sp2,al2 as ev2) ->
	let f1 i =
	  match ise_stack2 false env i (evar_conv_x ts) sk1 sk2 with
	  |None, Success i' -> 
	    (* Evar can be defined in i' *)
	    let ev1' = whd_evar i' (mkEvar ev1) in
	      if isEvar ev1' then
		solve_simple_eqn (evar_conv_x ts) env i'
		  (position_problem true pbty,destEvar ev1',term2)
	      else 
		evar_eqappr_x ts env evd pbty 
		  ((ev1', sk1), csts1) ((term2, sk2), csts2)
	  |Some (r,[]), Success i' -> 
	    let ev2' = whd_evar i' (mkEvar ev2) in
	      if isEvar ev2' then
		solve_simple_eqn (evar_conv_x ts) env i'
		  (position_problem false pbty,destEvar ev2',Stack.zip(term1,r))
	      else 
		evar_eqappr_x ts env evd pbty 
		  ((ev2', sk1), csts1) ((term2, sk2), csts2)

	  |Some ([],r), Success i' -> 
	    let ev1' = whd_evar i' (mkEvar ev1) in
	      if isEvar ev1' then
		solve_simple_eqn (evar_conv_x ts) env i'
	          (position_problem true pbty,destEvar ev1',Stack.zip(term2,r))
	      else evar_eqappr_x ts env evd pbty 
		((ev1', sk1), csts1) ((term2, sk2), csts2)
	  |_, (UnifFailure _ as x) -> x
	  |Some _, _ -> UnifFailure (i,NotSameArgSize)
	and f2 i =
          if Evar.equal sp1 sp2 then
	    match ise_stack2 false env i (evar_conv_x ts) sk1 sk2 with
	    |None, Success i' ->
              Success (solve_refl (fun env i pbty a1 a2 ->
                is_success (evar_conv_x ts env i pbty a1 a2))
                env i' (position_problem true pbty) sp1 al1 al2)
	    |_, (UnifFailure _ as x) -> x
            |Some _, _ -> UnifFailure (i,NotSameArgSize)
          else UnifFailure (i,NotSameHead)
	in
	ise_try evd [f1; f2]

    | Flexible ev1, MaybeFlexible v2 ->
      flex_maybeflex true ev1 (appr1,csts1) (appr2,csts2) v2

    | MaybeFlexible v1, Flexible ev2 -> 
      flex_maybeflex false ev2 (appr2,csts2) (appr1,csts1) v1

    | MaybeFlexible v1, MaybeFlexible v2 -> begin
        match kind_of_term term1, kind_of_term term2 with
        | LetIn (na,b1,t1,c'1), LetIn (_,b2,t2,c'2) ->
        let f1 i =
          ise_and i
	    [(fun i -> evar_conv_x ts env i CONV b1 b2);
	     (fun i ->
	       let b = nf_evar i b1 in
	       let t = nf_evar i t1 in
	       evar_conv_x ts (push_rel (na,Some b,t) env) i pbty c'1 c'2);
	     (fun i -> exact_ise_stack2 env i (evar_conv_x ts) sk1 sk2)]
	and f2 i =
          let out1 = whd_betaiota_deltazeta_for_iota_state (fst ts) env i csts1 (v1,sk1)
          and out2 = whd_betaiota_deltazeta_for_iota_state (fst ts) env i csts2 (v2,sk2)
	  in evar_eqappr_x ts env i pbty out1 out2
	in
	ise_try evd [f1; f2]

	| Proj (p, c), Proj (p', c') 
	  when Constant.equal (Projection.constant p) (Projection.constant p') ->
	  let f1 i = 
	    ise_and i 
	    [(fun i -> evar_conv_x ts env i CONV c c');
	     (fun i -> exact_ise_stack2 env i (evar_conv_x ts) sk1 sk2)]
	  and f2 i =
            let out1 = whd_betaiota_deltazeta_for_iota_state (fst ts) env i csts1 (v1,sk1)
            and out2 = whd_betaiota_deltazeta_for_iota_state (fst ts) env i csts2 (v2,sk2)
	    in evar_eqappr_x ts env i pbty out1 out2
	  in
	    ise_try evd [f1; f2]
	      
	(* Catch the p.c ~= p c' cases *)
	| Proj (p,c), Const (p',u) when eq_constant (Projection.constant p) p' ->
	  let res = 
	    try Some (destApp (Retyping.expand_projection env evd p c []))
	    with Retyping.RetypeError _ -> None
	  in
	    (match res with 
	    | Some (f1,args1) -> 
	      evar_eqappr_x ts env evd pbty ((f1,Stack.append_app args1 sk1),csts1) 
		(appr2,csts2)
	    | None -> UnifFailure (evd,NotSameHead))
	      
	| Const (p,u), Proj (p',c') when eq_constant p (Projection.constant p') ->
	  let res = 
	    try Some (destApp (Retyping.expand_projection env evd p' c' []))
	    with Retyping.RetypeError _ -> None
	  in 
	    (match res with
	    | Some (f2,args2) ->
	      evar_eqappr_x ts env evd pbty (appr1,csts1) ((f2,Stack.append_app args2 sk2),csts2)
	    | None -> UnifFailure (evd,NotSameHead))
	      
	| _, _ ->
	let f1 i = 
	  (* Gather the universe constraints that would make term1 and term2 equal.
	     If these only involve unifications of flexible universes to other universes,
	     allow this identification (first-order unification of universes). Otherwise
	     fallback to unfolding.
	  *)
	  let b,univs = Universes.eq_constr_universes term1 term2 in
	    if b then
	      ise_and i [(fun i -> 
		try Success (Evd.add_universe_constraints i univs)
		with UniversesDiffer -> UnifFailure (i,NotSameHead)
		| Univ.UniverseInconsistency p -> UnifFailure (i, UnifUnivInconsistency p));
			 (fun i -> exact_ise_stack2 env i (evar_conv_x ts) sk1 sk2)]
	    else UnifFailure (i,NotSameHead)
	and f2 i =
	  (try 
	     if not (snd ts) then raise Not_found
	     else conv_record ts env i
               (try check_conv_record env i appr1 appr2
		with Not_found -> check_conv_record env i appr2 appr1)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
	and f3 i =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) or the second argument is potentially
             usable as a canonical projection or canonical value *)
          let rec is_unnamed (hd, args) = match kind_of_term hd with
            | (Var _|Construct _|Ind _|Const _|Prod _|Sort _) ->
	      Stack.not_purely_applicative args
            | (CoFix _|Meta _|Rel _)-> true
            | Evar _ -> Stack.not_purely_applicative args
	    (* false (* immediate solution without Canon Struct *)*)
            | Lambda _ -> assert (match args with [] -> true | _ -> false); true
            | LetIn (_,b,_,c) -> is_unnamed
	     (fst (whd_betaiota_deltazeta_for_iota_state
		      (fst ts) env i Cst_stack.empty (subst1 b c, args)))
	    | Fix _ -> true (* Partially applied fix can be the result of a whd call *)
	    | Proj (p, _) -> Projection.unfolded p || Stack.not_purely_applicative args
            | Case _ | App _| Cast _ -> assert false in
          let rhs_is_stuck_and_unnamed () =
	    let applicative_stack = fst (Stack.strip_app sk2) in
	    is_unnamed
	      (fst (whd_betaiota_deltazeta_for_iota_state
		      (fst ts) env i Cst_stack.empty (v2, applicative_stack))) in
          let rhs_is_already_stuck =
            rhs_is_already_stuck || rhs_is_stuck_and_unnamed () in

	  if (isLambda term1 || rhs_is_already_stuck)
	    && (not (Stack.not_purely_applicative sk1)) then
	    evar_eqappr_x ~rhs_is_already_stuck ts env i pbty
	      (whd_betaiota_deltazeta_for_iota_state
		 (fst ts) env i (Cst_stack.add_cst term1 csts1) (v1,sk1))
	      (appr2,csts2)
	  else
	    evar_eqappr_x ts env i pbty (appr1,csts1)
	      (whd_betaiota_deltazeta_for_iota_state
		 (fst ts) env i (Cst_stack.add_cst term2 csts2) (v2,sk2))
	in
	ise_try evd [f1; f2; f3]
    end

    | Rigid, Rigid when isLambda term1 && isLambda term2 ->
        let (na,c1,c'1) = destLambda term1 in
        let (_,c2,c'2) = destLambda term2 in
        assert app_empty;
        ise_and evd
          [(fun i -> evar_conv_x ts env i CONV c1 c2);
           (fun i ->
	     let c = nf_evar i c1 in
	     evar_conv_x ts (push_rel (na,None,c) env) i CONV c'1 c'2)]

    | Flexible ev1, Rigid -> flex_rigid true ev1 appr1 appr2
    | Rigid, Flexible ev2 -> flex_rigid false ev2 appr2 appr1

    | MaybeFlexible v1, Rigid ->
	let f3 i =
	  (try 
	     if not (snd ts) then raise Not_found
	     else conv_record ts env i (check_conv_record env i appr1 appr2)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
	and f4 i =
	  evar_eqappr_x ts env i pbty
	    (whd_betaiota_deltazeta_for_iota_state
	       (fst ts) env i (Cst_stack.add_cst term1 csts1) (v1,sk1))
	    (appr2,csts2)
	in
	  ise_try evd [f3; f4]

    | Rigid, MaybeFlexible v2 ->
	let f3 i =
	  (try
	     if not (snd ts) then raise Not_found
	     else conv_record ts env i (check_conv_record env i appr2 appr1)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
	and f4 i =
	  evar_eqappr_x ts env i pbty (appr1,csts1)
	    (whd_betaiota_deltazeta_for_iota_state
	       (fst ts) env i (Cst_stack.add_cst term2 csts2) (v2,sk2))
	in
	  ise_try evd [f3; f4]

    (* Eta-expansion *)
    | Rigid, _ when isLambda term1 ->
        eta env evd true sk1 term1 sk2 term2

    | _, Rigid when isLambda term2 ->
        eta env evd false sk2 term2 sk1 term1

    | Rigid, Rigid -> begin
        match kind_of_term term1, kind_of_term term2 with

	| Sort s1, Sort s2 when app_empty ->
	    (try
	       let evd' =
		 if pbty == CONV
		 then Evd.set_eq_sort env evd s1 s2
		 else Evd.set_leq_sort env evd s1 s2
	       in Success evd'
	     with Univ.UniverseInconsistency p ->
               UnifFailure (evd,UnifUnivInconsistency p)
	     | e when Errors.noncritical e -> UnifFailure (evd,NotSameHead))

	| Prod (n,c1,c'1), Prod (_,c2,c'2) when app_empty ->
            ise_and evd
              [(fun i -> evar_conv_x ts env i CONV c1 c2);
               (fun i ->
 	         let c = nf_evar i c1 in
	         evar_conv_x ts (push_rel (n,None,c) env) i pbty c'1 c'2)]

	| Rel x1, Rel x2 ->
	    if Int.equal x1 x2 then
              exact_ise_stack2 env evd (evar_conv_x ts) sk1 sk2
            else UnifFailure (evd,NotSameHead)

	| Var var1, Var var2 ->
	    if Id.equal var1 var2 then
              exact_ise_stack2 env evd (evar_conv_x ts) sk1 sk2
            else UnifFailure (evd,NotSameHead)

	| Const _, Const _
	| Ind _, Ind _ 
	| Construct _, Construct _ ->
	  rigids env evd sk1 term1 sk2 term2

	| Construct u, _ ->
	  eta_constructor ts env evd sk1 u sk2 term2
	    
	| _, Construct u ->
	  eta_constructor ts env evd sk2 u sk1 term1

	| Fix ((li1, i1),(_,tys1,bds1 as recdef1)), Fix ((li2, i2),(_,tys2,bds2)) -> (* Partially applied fixs *)
	  if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
            ise_and evd [
	      (fun i -> ise_array2 i (fun i' -> evar_conv_x ts env i' CONV) tys1 tys2);
	      (fun i -> ise_array2 i (fun i' -> evar_conv_x ts (push_rec_types recdef1 env) i' CONV) bds1 bds2);
	      (fun i -> exact_ise_stack2 env i (evar_conv_x ts) sk1 sk2)]
	  else UnifFailure (evd, NotSameHead)

	| CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
            if Int.equal i1 i2  then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x ts env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x ts (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
                 (fun i -> exact_ise_stack2 env i
                     (evar_conv_x ts) sk1 sk2)]
            else UnifFailure (evd,NotSameHead)

	| (Meta _, _) | (_, Meta _) ->
	  begin match ise_stack2 true env evd (evar_conv_x ts) sk1 sk2 with
	  |_, (UnifFailure _ as x) -> x
	  |None, Success i' -> evar_conv_x ts env i' CONV term1 term2
	  |Some (sk1',sk2'), Success i' -> evar_conv_x ts env i' CONV (Stack.zip (term1,sk1')) (Stack.zip (term2,sk2'))
	  end

	| (Ind _ | Sort _ | Prod _ | CoFix _ | Fix _ | Rel _ | Var _ | Const _), _ ->
	  UnifFailure (evd,NotSameHead)
	| _, (Ind _ | Sort _ | Prod _ | CoFix _ | Fix _ | Rel _ | Var _ | Const _) ->
	  UnifFailure (evd,NotSameHead)

	| (App _ | Cast _ | Case _ | Proj _), _ -> assert false
	| (LetIn _| Evar _), _ -> assert false
	| (Lambda _), _ -> assert false

      end

and conv_record trs env evd (ctx,(h,h2),c,bs,(params,params1),(us,us2),(sk1,sk2),c1,(n,t2)) =
  (* Tries to unify the states

        (proji params1 c1 | sk1)   =   (proji params2 (c (?xs:bs)) | sk2)

     and the terms

        h us  =  h2 us2

     where

     c = the constant for the canonical structure (i.e. some term of the form
         fun (xs:bs) => Build_R params v1 .. vi-1 (h us) vi+1 .. vn)
     bs = the types of the parameters of the canonical structure
     c1 = the main argument of the canonical projection
     sk1, sk2 = the surrounding stacks of the conversion problem
     params1, params2 = the params of the projection (empty if a primitive proj)

     knowing that

       (proji params1 c1 | sk1)   =   (h2 us2 | sk2)

     had to be initially resolved
  *)
  let evd = Evd.merge_context_set Evd.univ_flexible evd ctx in
  if Reductionops.Stack.compare_shape sk1 sk2 then
    let (evd',ks,_,test) =
      List.fold_left
	(fun (i,ks,m,test) b ->
	  if match n with Some n -> Int.equal m n | None -> false then
	    let ty = Retyping.get_type_of env i t2 in
	    let test i = evar_conv_x trs env i CUMUL ty (substl ks b) in
	      (i,t2::ks, m-1, test)
	  else
	    let dloc = (Loc.ghost,Evar_kinds.InternalHole) in
            let (i',ev) = new_evar env i ~src:dloc (substl ks b) in
	    (i', ev :: ks, m - 1,test))
	(evd,[],List.length bs,fun i -> Success i) bs
    in
    let app = mkApp (c, Array.rev_of_list ks) in
    ise_and evd'
      [(fun i ->
	exact_ise_stack2 env i
          (fun env' i' cpb x1 x -> evar_conv_x trs env' i' cpb x1 (substl ks x))
          params1 params);
       (fun i ->
	 exact_ise_stack2 env i
           (fun env' i' cpb u1 u -> evar_conv_x trs env' i' cpb u1 (substl ks u))
           us2 us);
       (fun i -> evar_conv_x trs env i CONV c1 app);
       (fun i -> exact_ise_stack2 env i (evar_conv_x trs) sk1 sk2);
       test;
       (fun i -> evar_conv_x trs env i CONV h2
	 (fst (decompose_app_vect (substl ks h))))]
  else UnifFailure(evd,(*dummy*)NotSameHead)

and eta_constructor ts env evd sk1 ((ind, i), u) sk2 term2 =
  let mib = lookup_mind (fst ind) env in
    match mib.Declarations.mind_record with
    | Some (Some (id, projs, pbs)) when mib.Declarations.mind_finite <> Decl_kinds.CoFinite -> 
      let pars = mib.Declarations.mind_nparams in
	(try 
	   let l1' = Stack.tail pars sk1 in
	   let l2' = 
	     let term = Stack.zip (term2,sk2) in 
	       List.map (fun p -> mkProj (Projection.make p false, term)) (Array.to_list projs)
	   in
	     exact_ise_stack2 env evd (evar_conv_x (fst ts, false)) l1' 
	       (Stack.append_app_list l2' Stack.empty)
	 with 
	 | Invalid_argument _ ->
	   (* Stack.tail: partially applied constructor *)
	   UnifFailure(evd,NotSameHead))
    | _ -> UnifFailure (evd,NotSameHead)

let evar_conv_x ts = evar_conv_x (ts, true)

(* Profiling *)
let evar_conv_x =
  if Flags.profile then
    let evar_conv_xkey = Profile.declare_profile "evar_conv_x" in
      Profile.profile6 evar_conv_xkey evar_conv_x
  else evar_conv_x

let evar_conv_hook_get, evar_conv_hook_set = Hook.make ~default:evar_conv_x ()

let evar_conv_x ts = Hook.get evar_conv_hook_get ts

let set_evar_conv f = Hook.set evar_conv_hook_set f


(* We assume here |l1| <= |l2| *)

let first_order_unification ts env evd (ev1,l1) (term2,l2) =
  let (deb2,rest2) = Array.chop (Array.length l2-Array.length l1) l2 in
  ise_and evd
    (* First compare extra args for better failure message *)
    [(fun i -> ise_array2 i (fun i -> evar_conv_x ts env i CONV) rest2 l1);
    (fun i ->
      (* Then instantiate evar unless already done by unifying args *)
      let t2 = mkApp(term2,deb2) in
      if is_defined i (fst ev1) then
	evar_conv_x ts env i CONV t2 (mkEvar ev1)
      else
	solve_simple_eqn ~choose:true (evar_conv_x ts) env i (None,ev1,t2))]

let choose_less_dependent_instance evk evd term args =
  let evi = Evd.find_undefined evd evk in
  let subst = make_pure_subst evi args in
  let subst' = List.filter (fun (id,c) -> Term.eq_constr c term) subst in
  match subst' with
  | [] -> None
  | (id, _) :: _ -> Some (Evd.define evk (mkVar id) evd)

let apply_on_subterm env evdref f c t =
  let rec applyrec (env,(k,c) as acc) t =
    (* By using eq_constr, we make an approximation, for instance, we *)
    (* could also be interested in finding a term u convertible to t *)
    (* such that c occurs in u *)
    if e_eq_constr_univs evdref c t then f k
    else
      match kind_of_term t with
      | Evar (evk,args) when Evd.is_undefined !evdref evk ->
          let ctx = evar_filtered_context (Evd.find_undefined !evdref evk) in
          let g (_,b,_) a = if Option.is_empty b then applyrec acc a else a in
          mkEvar (evk, Array.of_list (List.map2 g ctx (Array.to_list args)))
      | _ ->
        map_constr_with_binders_left_to_right
	  (fun d (env,(k,c)) -> (push_rel d env, (k+1,lift 1 c)))
	  applyrec acc t
  in
  applyrec (env,(0,c)) t

let filter_possible_projections c ty ctxt args =
  (* Since args in the types will be replaced by holes, we count the
     fv of args to have a well-typed filter; don't know how necessary
     it is however to have a well-typed filter here *)
  let fv1 = free_rels (mkApp (c,args)) (* Hack: locally untyped *) in
  let fv2 = collect_vars (mkApp (c,args)) in
  let len = Array.length args in
  let tyvars = collect_vars ty in
  List.map_i (fun i (id,b,_) ->
    let () = assert (i < len) in
    let a = Array.unsafe_get args i in
    (match b with None -> false | Some c -> not (isRel c || isVar c)) ||
    a == c ||
    (* Here we make an approximation, for instance, we could also be *)
    (* interested in finding a term u convertible to c such that a occurs *)
    (* in u *)
    isRel a && Int.Set.mem (destRel a) fv1 ||
    isVar a && Id.Set.mem (destVar a) fv2 ||
    Id.Set.mem id tyvars)
    0 ctxt

let solve_evars = ref (fun _ -> failwith "solve_evars not installed")
let set_solve_evars f = solve_evars := f

(* We solve the problem env_rhs |- ?e[u1..un] = rhs knowing
 * x1:T1 .. xn:Tn |- ev : ty
 * by looking for a maximal well-typed abtraction over u1..un in rhs
 *
 * We first build C[e11..e1p1,..,en1..enpn] obtained from rhs by replacing
 * all occurrences of u1..un by evars eij of type Ti' where itself Ti' has
 * been obtained from the type of ui by also replacing all occurrences of
 * u1..ui-1 by evars.
 *
 * Then, we use typing to infer the relations between the different
 * occurrences. If some occurrence is still unconstrained after typing,
 * we instantiate successively the unresolved occurrences of un by xn,
 * of un-1 by xn-1, etc [the idea comes from Chung-Kil Hur, that he
 * used for his Heq plugin; extensions to several arguments based on a
 * proposition from Dan Grayson]
 *)

exception TypingFailed of evar_map

let second_order_matching ts env_rhs evd (evk,args) argoccs rhs =
  try
  let evi = Evd.find_undefined evd evk in
  let env_evar = evar_filtered_env evi in
  let sign = named_context_val env_evar in
  let ctxt = evar_filtered_context evi in
  let instance = List.map mkVar (List.map pi1 ctxt) in

  let rec make_subst = function
  | (id,_,t)::ctxt', c::l, occs::occsl when isVarId id c ->
      begin match occs with
      | Some _ ->
        error "Cannot force abstraction on identity instance."
      | None ->
        make_subst (ctxt',l,occsl)
      end
  | (id,_,t)::ctxt', c::l, occs::occsl ->
      let evs = ref [] in
      let ty = Retyping.get_type_of env_rhs evd c in
      let filter' = filter_possible_projections c ty ctxt args in
      (id,t,c,ty,evs,Filter.make filter',occs) :: make_subst (ctxt',l,occsl)
  | _, _, [] -> []
  | _ -> anomaly (Pp.str "Signature or instance are shorter than the occurrences list") in

  let rec set_holes evdref rhs = function
  | (id,_,c,cty,evsref,filter,occs)::subst ->
      let set_var k =
        match occs with
        | Some Locus.AllOccurrences -> mkVar id
        | Some _ -> error "Selection of specific occurrences not supported"
        | None ->
        let evty = set_holes evdref cty subst in
        let instance = Filter.filter_list filter instance in
        let evd,ev = new_evar_instance sign !evdref evty ~filter instance in
        evdref := evd;
        evsref := (fst (destEvar ev),evty)::!evsref;
        ev in
      set_holes evdref (apply_on_subterm env_rhs evdref set_var c rhs) subst
  | [] -> rhs in

  let subst = make_subst (ctxt,Array.to_list args,argoccs) in

  let evdref = ref evd in
  let rhs = set_holes evdref rhs subst in
  let evd = !evdref in

  (* We instantiate the evars of which the value is forced by typing *)
  let evd,rhs =
    let evdref = ref evd in
    try let c = !solve_evars env_evar evdref rhs in !evdref,c
    with e when Pretype_errors.precatchable_exception e ->
      (* Could not revert all subterms *)
      raise (TypingFailed !evdref) in

  let rec abstract_free_holes evd = function
  | (id,idty,c,_,evsref,_,_)::l ->
      let rec force_instantiation evd = function
      | (evk,evty)::evs ->
          let evd =
            if is_undefined evd evk then
              (* We force abstraction over this unconstrained occurrence *)
              (* and we use typing to propagate this instantiation *)
              (* This is an arbitrary choice *)
              let evd = Evd.define evk (mkVar id) evd in
              match evar_conv_x ts env_evar evd CUMUL idty evty with
              | UnifFailure _ -> error "Cannot find an instance"
              | Success evd ->
              match reconsider_conv_pbs (evar_conv_x ts) evd with
              | UnifFailure _ -> error "Cannot find an instance"
              | Success evd ->
              evd
            else
              evd
          in
          force_instantiation evd evs
      | [] ->
          abstract_free_holes evd l
      in
      force_instantiation evd !evsref
  | [] ->
    let evd = 
      try Evarsolve.check_evar_instance evd evk rhs 
	    (evar_conv_x full_transparent_state)
      with IllTypedInstance _ -> raise (TypingFailed evd)
    in
      Evd.define evk rhs evd 
  in
  abstract_free_holes evd subst, true
  with TypingFailed evd -> evd, false

let second_order_matching_with_args ts env evd ev l t =
(*
  let evd,ev = evar_absorb_arguments env evd ev l in
  let argoccs = Array.map_to_list (fun _ -> None) (snd ev) in
  let evd, b = second_order_matching ts env evd ev argoccs t in
  if b then Success evd
  else UnifFailure (evd, ConversionFailed (env,mkApp(mkEvar ev,l),t))
  if b then Success evd else
*)
  UnifFailure (evd, ConversionFailed (env,mkApp(mkEvar ev,l),t))

let apply_conversion_problem_heuristic ts env evd pbty t1 t2 =
  let t1 = apprec_nohdbeta ts env evd (whd_head_evar evd t1) in
  let t2 = apprec_nohdbeta ts env evd (whd_head_evar evd t2) in
  let (term1,l1 as appr1) = try destApp t1 with DestKO -> (t1, [||]) in
  let (term2,l2 as appr2) = try destApp t2 with DestKO -> (t2, [||]) in
  let app_empty = Array.is_empty l1 && Array.is_empty l2 in
  match kind_of_term term1, kind_of_term term2 with
  | Evar (evk1,args1), (Rel _|Var _) when app_empty
      && List.for_all (fun a -> Term.eq_constr a term2 || isEvar a)
        (remove_instance_local_defs evd evk1 args1) ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      (match choose_less_dependent_instance evk1 evd term2 args1 with
      | Some evd -> Success evd
      | None -> UnifFailure (evd, ConversionFailed (env,term1,term2)))
  | (Rel _|Var _), Evar (evk2,args2) when app_empty
      && List.for_all (fun a -> Term.eq_constr a term1 || isEvar a)
        (remove_instance_local_defs evd evk2 args2) ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      (match choose_less_dependent_instance evk2 evd term1 args2 with
      | Some evd -> Success evd
      | None -> UnifFailure (evd, ConversionFailed (env,term1,term2)))
  | Evar (evk1,args1), Evar (evk2,args2) when Evar.equal evk1 evk2 ->
      let f env evd pbty x y = is_trans_fconv pbty ts env evd x y in
      Success (solve_refl ~can_drop:true f env evd
                 (position_problem true pbty) evk1 args1 args2)
  | Evar ev1, Evar ev2 ->
      Success (solve_evar_evar ~force:true
        (evar_define (evar_conv_x ts) ~choose:true) (evar_conv_x ts) env evd
        (position_problem true pbty) ev1 ev2)
  | Evar ev1,_ when Array.length l1 <= Array.length l2 ->
      (* On "?n t1 .. tn = u u1 .. u(n+p)", try first-order unification *)
      (* and otherwise second-order matching *)
      ise_try evd
        [(fun evd -> first_order_unification ts env evd (ev1,l1) appr2);
         (fun evd ->
           second_order_matching_with_args ts env evd ev1 l1 t2)]
  | _,Evar ev2 when Array.length l2 <= Array.length l1 ->
      (* On "u u1 .. u(n+p) = ?n t1 .. tn", try first-order unification *)
      (* and otherwise second-order matching *)
      ise_try evd
        [(fun evd -> first_order_unification ts env evd (ev2,l2) appr1);
         (fun evd ->
           second_order_matching_with_args ts env evd ev2 l2 t1)]
  | Evar ev1,_ ->
      (* Try second-order pattern-matching *)
      second_order_matching_with_args ts env evd ev1 l1 t2
  | _,Evar ev2 ->
      (* Try second-order pattern-matching *)
      second_order_matching_with_args ts env evd ev2 l2 t1
  | _ ->
      (* Some head evar have been instantiated, or unknown kind of problem *)
      evar_conv_x ts env evd pbty t1 t2

let check_problems_are_solved env evd =
  match snd (extract_all_conv_pbs evd) with
  | (pbty,env,t1,t2)::_ -> Pretype_errors.error_cannot_unify env evd (t1, t2)
  | _ -> ()

let max_undefined_with_candidates evd =
  (* If evar were ordered with highest index first, fold_undefined
     would be going decreasingly and we could use fold_undefined to
     find the undefined evar of maximum index (alternatively,
     max_bindings from ocaml 3.12 could be used); instead we traverse
     the whole map *)
  let l = Evd.fold_undefined
    (fun evk ev_info evars ->
        match ev_info.evar_candidates with
        | None -> evars
        | Some l -> (evk,ev_info,l)::evars) evd [] in
  match l with
  | [] -> None
  | a::l -> Some (List.last (a::l))

let rec solve_unconstrained_evars_with_candidates ts evd =
  (* max_undefined is supposed to return the most recent, hence
     possibly most dependent evar *)
  match max_undefined_with_candidates evd with
  | None -> evd
  | Some (evk,ev_info,l) ->
      let rec aux = function
      | [] -> error "Unsolvable existential variables."
      | a::l ->
          try
            let conv_algo = evar_conv_x ts in
            let evd = check_evar_instance evd evk a conv_algo in
            let evd = Evd.define evk a evd in
            match reconsider_conv_pbs conv_algo evd with
            | Success evd -> solve_unconstrained_evars_with_candidates ts evd
            | UnifFailure _ -> aux l
          with
          | IllTypedInstance _ -> aux l
          | e when Pretype_errors.precatchable_exception e -> aux l in
      (* List.rev is there to favor most dependent solutions *)
      (* and favor progress when used with the refine tactics *)
      let evd = aux (List.rev l) in
      solve_unconstrained_evars_with_candidates ts evd

let solve_unconstrained_impossible_cases env evd =
  Evd.fold_undefined (fun evk ev_info evd' ->
    match ev_info.evar_source with
    | _,Evar_kinds.ImpossibleCase -> 
      let j, ctx = coq_unit_judge () in
      let evd' = Evd.merge_context_set Evd.univ_flexible_alg evd' ctx in
      let ty = j_type j in
      let conv_algo = evar_conv_x full_transparent_state in
      let evd' = check_evar_instance evd' evk ty conv_algo in
	Evd.define evk ty evd' 
    | _ -> evd') evd evd

let consider_remaining_unif_problems env
    ?(ts=Conv_oracle.get_transp_state (Environ.oracle env)) evd =
  let evd = solve_unconstrained_evars_with_candidates ts evd in
  let rec aux evd pbs progress stuck =
    match pbs with
    | (pbty,env,t1,t2 as pb) :: pbs ->
        (match apply_conversion_problem_heuristic ts env evd pbty t1 t2 with
	| Success evd' ->
	    let (evd', rest) = extract_all_conv_pbs evd' in
            begin match rest with
            | [] -> aux evd' pbs true stuck
            | _ -> (* Unification got actually stuck, postpone *)
	      aux evd pbs progress (pb :: stuck)
            end
        | UnifFailure (evd,reason) ->
	    Pretype_errors.error_cannot_unify_loc (loc_of_conv_pb evd pb)
              env evd ~reason (t1, t2))
    | _ -> 
	if progress then aux evd stuck false []
	else 
	  match stuck with
	  | [] -> (* We're finished *) evd
	  | (pbty,env,t1,t2 as pb) :: _ ->
	      (* There remains stuck problems *)
	      Pretype_errors.error_cannot_unify_loc (loc_of_conv_pb evd pb)
                env evd (t1, t2)
  in
  let (evd,pbs) = extract_all_conv_pbs evd in
  let heuristic_solved_evd = aux evd pbs false [] in
  check_problems_are_solved env heuristic_solved_evd;
  solve_unconstrained_impossible_cases env heuristic_solved_evd

(* Main entry points *)

exception UnableToUnify of evar_map * unification_error

let default_transparent_state env = full_transparent_state
(* Conv_oracle.get_transp_state (Environ.oracle env) *)

let the_conv_x env ?(ts=default_transparent_state env) t1 t2 evd =
  match evar_conv_x ts env evd CONV  t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let the_conv_x_leq env ?(ts=default_transparent_state env) t1 t2 evd =
  match evar_conv_x ts env evd CUMUL t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let e_conv env ?(ts=default_transparent_state env) evdref t1 t2 =
  match evar_conv_x ts env !evdref CONV t1 t2 with
  | Success evd' -> evdref := evd'; true
  | _ -> false

let e_cumul env ?(ts=default_transparent_state env) evdref t1 t2 =
  match evar_conv_x ts env !evdref CUMUL t1 t2 with
  | Success evd' -> evdref := evd'; true
  | _ -> false
