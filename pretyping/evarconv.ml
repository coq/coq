(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Names
open Term
open Termops
open Environ
open EConstr
open Vars
open CClosure
open Reduction
open Reductionops
open Recordops
open Evarutil
open Evardefine
open Evarsolve
open Evd
open Pretype_errors

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type unify_flags = Evarsolve.unify_flags

type unify_fun = unify_flags ->
  env -> evar_map -> conv_pb -> EConstr.constr -> EConstr.constr -> Evarsolve.unification_result

let default_transparent_state env = full_transparent_state
(* Conv_oracle.get_transp_state (Environ.oracle env) *)

let default_flags_of ?(subterm_ts=empty_transparent_state) ts =
  { modulo_betaiota = true;
    open_ts = ts; closed_ts = ts; subterm_ts;
    frozen_evars = Evar.Set.empty; with_cs = true;
    allow_K_at_toplevel = true }

let default_flags env =
  let ts = default_transparent_state env in
  default_flags_of ts

let debug_unification = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname =
    "Print states sent to Evarconv unification";
  Goptions.optkey = ["Debug";"Unification"];
  Goptions.optread = (fun () -> !debug_unification);
  Goptions.optwrite = (fun a -> debug_unification:=a);
}

let debug_ho_unification = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname =
    "Print debug information for the higer-order unification algorithm";
  Goptions.optkey = ["Debug";"HO"; "Unification"];
  Goptions.optread = (fun () -> !debug_ho_unification);
  Goptions.optwrite = (fun a -> debug_ho_unification:=a);
}

(*******************************************)
(* Functions to deal with impossible cases *)
(*******************************************)
(* XXX: we would like to search for this with late binding
   "data.id.type" etc... *)
let impossible_default_case () =
  let c, ctx = Universes.fresh_global_instance (Global.env()) (Globnames.ConstRef Coqlib.id) in
  let (_, u) = Term.destConst c in
  Some (c, Term.mkConstU (Coqlib.type_of_id, u), ctx)

let coq_unit_judge =
  let open Environ in
  let make_judge c t = make_judge (EConstr.of_constr c) (EConstr.of_constr t) in
  let na1 = Name (Id.of_string "A") in
  let na2 = Name (Id.of_string "H") in
  fun () ->
    match impossible_default_case () with
    | Some (id, type_of_id, ctx) ->
      make_judge id type_of_id, ctx
    | None ->
      (* In case the constants id/ID are not defined *)
      Environ.make_judge (mkLambda (na1,mkProp,mkLambda(na2,mkRel 1,mkRel 1)))
        (mkProd (na1,mkProp,mkArrow (mkRel 1) (mkRel 2))), 
      Univ.ContextSet.empty

let to_pb (pb, env, t1, t2) =
  (pb, env, EConstr.Unsafe.to_constr t1, EConstr.Unsafe.to_constr t2)

let unfold_projection env evd ts p c =
  let cst = Projection.constant p in
    if is_transparent_constant ts cst then
      Some (mkProj (Projection.make cst true, c))
    else None
      
let eval_flexible_term ts env evd c =
  match EConstr.kind evd c with
  | Const (c, u) ->
      if is_transparent_constant ts c
      then Option.map EConstr.of_constr (constant_opt_value_in env (c, EInstance.kind evd u))
      else None
  | Rel n ->
      (try match lookup_rel n env with
           | RelDecl.LocalAssum _ -> None
           | RelDecl.LocalDef (_,v,_) -> Some (lift n v)
       with Not_found -> None)
  | Var id ->
      (try
	 if is_transparent_variable ts id then
	   env |> lookup_named id |> NamedDecl.get_value
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
  | MaybeFlexible of EConstr.t (* reducible but not necessarily reduced *)
  | Flexible of EConstr.existential

let is_frozen flags (evk, _) = Evar.Set.mem evk flags.frozen_evars

let flex_kind_of_term flags env evd c sk =
  match EConstr.kind evd c with
    | LetIn _ | Rel _ | Const _ | Var _ | Proj _ ->
      Option.cata (fun x -> MaybeFlexible x) Rigid (eval_flexible_term flags.open_ts env evd c)
    | Lambda _ when not (Option.is_empty (Stack.decomp sk)) ->
       if flags.modulo_betaiota then MaybeFlexible c
       else Rigid
    | Evar ev ->
       if is_frozen flags ev then Rigid
       else Flexible ev
    | Lambda _ | Prod _ | Sort _ | Ind _ | Construct _ | CoFix _ -> Rigid
    | Meta _ -> Rigid
    | Fix _ -> Rigid (* happens when the fixpoint is partially applied *)
    | Cast _ | App _ | Case _ -> assert false

let apprec_nohdbeta flags env evd c =
  let (t,sk as appr) = Reductionops.whd_nored_state evd (c, []) in
  if flags.modulo_betaiota && Stack.not_purely_applicative sk
  then Stack.zip evd (fst (whd_betaiota_deltazeta_for_iota_state
		   flags.open_ts env evd Cst_stack.empty appr))
  else c

let position_problem l2r = function
  | CONV -> None
  | CUMUL -> Some l2r

(* [occur_rigidly ev evd t] tests if the evar ev occurs in a rigid
   context in t 

  That function should be an over approximation of occur-check, it can
  return true even if the occur-check would fail on the normal form, as
  otherwise we will postpone unsolvable constraints while maybe a
  reduction would have allowed unification (see bug 3539 for example). 

  The boolean indicates if the term is a rigid head. For applications,
  this means than an occurrence of the evar in arguments should be looked
  at to find an occur-check.

  TODO: replace with a test on the normal form and evaluate performance.
 *)
let occur_rigidly (evk,_ as ev) evd t = 
  let rec aux t =
    match EConstr.kind evd t with
    | App (f, c) -> if aux f then Array.exists aux c else false
    | Construct _ | Ind _ | Sort _ | Meta _ | Fix _ | CoFix _ -> true
    | Proj (p, c) -> not (aux c)
    | Evar (evk',_) -> if Evar.equal evk evk' then raise Occur else false
    | Cast (p, _, _) -> aux p
    | Lambda (na, t, b) -> aux b
    | LetIn (na, _, _, b) -> aux b
    | Const _ -> false
    | Prod (_, b, t) -> ignore(aux b || aux t); true
    | Rel _ | Var _ -> false
    | Case (_,_,c,_) -> if eq_constr evd (mkEvar ev) c then raise Occur else false
  in try ignore(aux t); false with Occur -> true

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
  let (proji, u), arg = Termops.global_app_of_constr sigma t1 in
  let canon_s,sk2_effective =
    try
      match EConstr.kind sigma t2 with
	Prod (_,a,b) -> (* assert (l2=[]); *)
	  let _, a, b = destProd sigma t2 in
          if noccurn sigma 1 b then
            lookup_canonical_conversion (proji, Prod_cs),
	    (Stack.append_app [|a;pop b|] Stack.empty)
          else raise Not_found
      | Sort s ->
        let s = ESorts.kind sigma s in
	lookup_canonical_conversion
	  (proji, Sort_cs (family_of_sort s)),[]
      | _ ->
	let (c2, _) = Termops.global_of_constr sigma t2 in
	  lookup_canonical_conversion (proji, Const_cs c2),sk2
    with Not_found ->
      let (c, cs) = lookup_canonical_conversion (proji,Default_cs) in 
	(c,cs),[]
  in
  let t', { o_DEF = c; o_CTX = ctx; o_INJ=n; o_TABS = bs;
        o_TPARAMS = params; o_NPARAMS = nparams; o_TCOMPS = us } = canon_s in
  let us = List.map EConstr.of_constr us in
  let params = List.map EConstr.of_constr params in
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
  let u, ctx' = Universes.fresh_instance_from ctx None in
  let subst = Univ.make_inverse_instance_subst u in
  let c = EConstr.of_constr c in
  let c' = subst_univs_level_constr subst c in
  let t' = EConstr.of_constr t' in
  let t' = subst_univs_level_constr subst t' in
  let bs' = List.map (EConstr.of_constr %> subst_univs_level_constr subst) bs in
  let h, _ = decompose_app_vect sigma t' in
    ctx',(h, t2),c',bs',(Stack.append_app_list params Stack.empty,params1),
    (Stack.append_app_list us Stack.empty,us2),(extra_args1,extra_args2),c1,
    (n, Stack.zip sigma (t2,sk2))

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

let push_rec_types pfix env =
  let (i, c, t) = pfix in
  let inj c = EConstr.Unsafe.to_constr c in
  push_rec_types (i, Array.map inj c, Array.map inj t) env

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

let check_leq_inductives evd cumi u u' =
  let u = EConstr.EInstance.kind evd u in
  let u' = EConstr.EInstance.kind evd u' in
  let length_ind_instance =
    Univ.AUContext.size (Univ.ACumulativityInfo.univ_context cumi)
  in
  let ind_sbcst =  Univ.ACumulativityInfo.subtyp_context cumi in
  if not ((length_ind_instance = Univ.Instance.length u) &&
          (length_ind_instance = Univ.Instance.length u')) then
     anomaly (Pp.str "Invalid inductive subtyping encountered!")
  else
    begin
     let comp_subst = (Univ.Instance.append u u') in
     let comp_cst =  Univ.AUContext.instantiate comp_subst ind_sbcst in
     Evd.add_constraints evd comp_cst
    end

let conv_fun f flags on_types =
  let typefn env evd pbty term1 term2 =
    f { (default_flags env) with with_cs = flags.with_cs } env evd pbty term1 term2
  in
  let termfn env evd pbty term1 term2 =
    f flags env evd pbty term1 term2
  in if on_types then typefn else termfn

let rec evar_conv_x flags env evd pbty term1 term2 =
  let term1 = whd_head_evar evd term1 in
  let term2 = whd_head_evar evd term2 in
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]
     could have found, we do it only if the terms are free of evar.
     Note: incomplete heuristic... *)
  let ground_test =
    if is_ground_term evd term1 && is_ground_term evd term2 then (
      let e =
	try
	  let evd, b = infer_conv ~catch_incon:false ~pb:pbty ~ts:flags.closed_ts
	    env evd term1 term2 
	  in
	    if b then Success evd
	    else UnifFailure (evd, ConversionFailed (env,term1,term2))
	with Univ.UniverseInconsistency e -> UnifFailure (evd, UnifUnivInconsistency e)
      in
	match e with
	| UnifFailure (evd, e) when not (is_ground_env evd env) -> None
	| _ -> Some e)
    else None
  in
  match ground_test with
    | Some result -> result
    | None ->
      (* Until pattern-unification is used consistently, use nohdbeta to not
	   destroy beta-redexes that can be used for 1st-order unification *)
        let term1 = apprec_nohdbeta flags env evd term1 in
        let term2 = apprec_nohdbeta flags env evd term2 in
	let default () = 
          evar_eqappr_x flags env evd pbty
            (whd_nored_state evd (term1,Stack.empty), Cst_stack.empty)
            (whd_nored_state evd (term2,Stack.empty), Cst_stack.empty)
	in
          begin match EConstr.kind evd term1, EConstr.kind evd term2 with
          | Evar ev, _ when Evd.is_undefined evd (fst ev) && not (is_frozen flags ev) ->
            (match solve_simple_eqn flags (conv_fun evar_conv_x flags) env evd
              (position_problem true pbty,ev,term2) with
	      | UnifFailure (_,OccurCheck _) -> 
		(* Eta-expansion might apply *) default ()
	      | x -> x)
          | _, Evar ev when Evd.is_undefined evd (fst ev) && not (is_frozen flags ev) ->
            (match solve_simple_eqn flags (conv_fun evar_conv_x flags) env evd
              (position_problem false pbty,ev,term1) with
	      | UnifFailure (_, OccurCheck _) ->
		(* Eta-expansion might apply *) default () 
	      | x -> x)
          | _ -> default ()
        end

and evar_eqappr_x ?(rhs_is_already_stuck = false) flags env evd pbty
    ((term1,sk1 as appr1),csts1) ((term2,sk2 as appr2),csts2) =
  let quick_fail i = (* not costly, loses info *)
    UnifFailure (i, NotSameHead)
  in
  let miller_pfenning on_left fallback ev lF tM evd =
    match is_unification_pattern_evar env evd ev lF tM with
      | None -> fallback ()
      | Some l1' -> (* Miller-Pfenning's patterns unification *)
	let t2 = tM in
	let t2 = solve_pattern_eqn env evd l1' t2 in
	  solve_simple_eqn flags (conv_fun evar_conv_x flags) env evd
	    (position_problem on_left pbty,ev,t2) 
  in
  let consume_stack on_left (termF,skF) (termO,skO) evd =
    let switch f a b = if on_left then f a b else f b a in
    let not_only_app = Stack.not_purely_applicative skO in
    match switch (ise_stack2 not_only_app env evd (evar_conv_x flags)) skF skO with
      |Some (l,r), Success i' when on_left && (not_only_app || List.is_empty l) ->
	switch (evar_conv_x flags env i' pbty) (Stack.zip evd (termF,l)) (Stack.zip evd (termO,r))
      |Some (r,l), Success i' when not on_left && (not_only_app || List.is_empty l) ->
	switch (evar_conv_x flags env i' pbty) (Stack.zip evd (termF,l)) (Stack.zip evd (termO,r))
      |None, Success i' -> switch (evar_conv_x flags env i' pbty) termF termO
      |_, (UnifFailure _ as x) -> x
      |Some _, _ -> UnifFailure (evd,NotSameArgSize) in
  let eta env evd onleft sk term sk' term' =
    assert (match sk with [] -> true | _ -> false);
    let (na,c1,c'1) = destLambda evd term in
    let c = nf_evar evd c1 in
    let env' = push_rel (RelDecl.LocalAssum (na,c)) env in
    let out1 = whd_betaiota_deltazeta_for_iota_state
      flags.open_ts env' evd Cst_stack.empty (c'1, Stack.empty) in
    let out2 = whd_nored_state evd
      (Stack.zip evd (term', sk' @ [Stack.Shift 1]), Stack.append_app [|EConstr.mkRel 1|] Stack.empty), 
      Cst_stack.empty in
    if onleft then evar_eqappr_x flags env' evd CONV out1 out2
    else evar_eqappr_x flags env' evd CONV out2 out1
  in
  let rigids env evd sk term sk' term' =
    let check_strict () =
      let univs = EConstr.eq_constr_universes evd term term' in
      match univs with
      | Some univs ->
        begin
          let cstrs = Universes.to_constraints (Evd.universes evd) univs in
          try Success (Evd.add_constraints evd cstrs)
          with Univ.UniverseInconsistency p -> UnifFailure (evd, UnifUnivInconsistency p)
        end
      | None ->
        UnifFailure (evd, NotSameHead)
    in
    let first_try_strict_check cond u u' try_subtyping_constraints =
      if cond then
        let univs = EConstr.eq_constr_universes evd term term' in
        match univs with
        | Some univs ->
          begin
            let cstrs = Universes.to_constraints (Evd.universes evd) univs in
            try Success (Evd.add_constraints evd cstrs)
            with Univ.UniverseInconsistency p -> try_subtyping_constraints ()
          end
        | None ->
          UnifFailure (evd, NotSameHead)
      else
        UnifFailure (evd, NotSameHead)
    in
    let compare_heads evd = 
      match EConstr.kind evd term, EConstr.kind evd term' with
      | Const (c, u), Const (c', u') ->
        check_strict ()
      | Ind (ind, u), Ind (ind', u') ->
        let check_subtyping_constraints () =
          let nparamsaplied = Stack.args_size sk in
          let nparamsaplied' = Stack.args_size sk' in
          begin
            let mind = Environ.lookup_mind (fst ind) env in
            match mind.Declarations.mind_universes with
            | Declarations.Monomorphic_ind _ | Declarations.Polymorphic_ind _ ->
              UnifFailure (evd, NotSameHead)
            | Declarations.Cumulative_ind cumi ->
              begin
                let num_param_arity =
                  mind.Declarations.mind_nparams + 
                  mind.Declarations.mind_packets.(snd ind).Declarations.mind_nrealargs
                in
                if not (num_param_arity = nparamsaplied
                        && num_param_arity = nparamsaplied') then
                  UnifFailure (evd, NotSameHead)
                else
                  begin
                    let evd' = check_leq_inductives evd cumi u u' in
                    Success (check_leq_inductives evd' cumi u' u)
                  end
              end
          end
        in
        first_try_strict_check (Names.eq_ind ind ind') u u' check_subtyping_constraints
      | Construct (cons, u), Construct (cons', u') ->
        let check_subtyping_constraints () =
          let ind, ind' = fst cons, fst cons' in
          let j, j' = snd cons, snd cons' in
          let nparamsaplied = Stack.args_size sk in
          let nparamsaplied' = Stack.args_size sk' in
          let mind = Environ.lookup_mind (fst ind) env in
          match mind.Declarations.mind_universes with
          | Declarations.Monomorphic_ind _ | Declarations.Polymorphic_ind _ ->
            UnifFailure (evd, NotSameHead)
          | Declarations.Cumulative_ind cumi ->
            begin
              let num_cnstr_args =
                let nparamsctxt =
                  mind.Declarations.mind_nparams + 
                  mind.Declarations.mind_packets.(snd ind).Declarations.mind_nrealargs
                in
                nparamsctxt + 
                mind.Declarations.mind_packets.(snd ind).
                  Declarations.mind_consnrealargs.(j - 1)
              in
              if not (num_cnstr_args = nparamsaplied 
                      && num_cnstr_args = nparamsaplied') then
                UnifFailure (evd, NotSameHead)
              else
                begin
                  let evd' = check_leq_inductives evd cumi u u' in
                  Success (check_leq_inductives evd' cumi u' u)
                end
            end
        in
        first_try_strict_check (Names.eq_constructor cons cons') u u' check_subtyping_constraints
      | _, _ -> anomaly (Pp.str "")
    in
    ise_and evd [(fun i ->
                try compare_heads i
                with Univ.UniverseInconsistency p -> UnifFailure (i, UnifUnivInconsistency p));
                 (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk sk')]
  in
  let consume on_left (_, skF as apprF) (_,skM as apprM) i =
    if not (Stack.is_empty skF && Stack.is_empty skM) then
      consume_stack on_left apprF apprM i
    else quick_fail i
  in
  let miller on_left ev (termF,skF as apprF) (termM, skM as apprM) i =
    let switch f a b = if on_left then f a b else f b a in
    let not_only_app = Stack.not_purely_applicative skM in
      match Stack.list_of_app_stack skF with
      | None -> quick_fail evd
      | Some lF -> 
        let tM = Stack.zip evd apprM in
	  miller_pfenning on_left
	    (fun () -> if not_only_app then (* Postpone the use of an heuristic *)
	      switch (fun x y -> Success (Evarutil.add_unification_pb (pbty,env,x,y) i)) (Stack.zip evd apprF) tM
	    else quick_fail i)
	    ev lF tM i
  in
  let flex_maybeflex on_left ev ((termF,skF as apprF),cstsF) ((termM, skM as apprM),cstsM) vM =
    let switch f a b = if on_left then f a b else f b a in
    let delta i =
      switch (evar_eqappr_x flags env i pbty) (apprF,cstsF)
	(whd_betaiota_deltazeta_for_iota_state flags.open_ts env i cstsM (vM,skM))
    in    
    let default i = ise_try i [miller on_left ev apprF apprM;
                               consume on_left apprF apprM;
                               delta]
    in
      match EConstr.kind evd termM with
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
		    whd_betaiota_deltazeta_for_iota_state flags.open_ts env evd cstsM (termM',skM)
		  in
		  let delta' i = 
                    switch (evar_eqappr_x flags env i pbty) (apprF,cstsF) (apprM',cstsM')
		  in
		  fun i -> ise_try i [miller on_left ev apprF apprM';
                                   consume on_left apprF apprM'; delta']
		with Retyping.RetypeError _ ->
		(* Happens thanks to w_unify building ill-typed terms *) 
		  default
	      in f evd
	  end
      | _ -> default evd
  in
  let rec first_order flexrigid env i t1 t2 sk1 sk2 =
    (* Try first-order unification *)
    match ise_stack2 false env i (evar_conv_x flags) sk1 sk2 with
    | None, Success i' ->
       (* We do have sk1[] = sk2[]: we now unify ?ev1 and ?ev2 *)
       (* Note that ?ev1 and ?ev2, may have been instantiated in the meantime *)
       let ev1' = whd_evar i' t1 in
       if isEvar i' ev1' then
         solve_simple_eqn flags (conv_fun evar_conv_x flags) env i'
		          (position_problem true pbty,destEvar i' ev1',term2)
       else
         evar_eqappr_x flags env evd pbty
		       ((ev1', sk1), csts1) ((term2, sk2), csts2)
    | Some (r,[]), Success i' ->
       (* We have sk1'[] = sk2[] for some sk1' s.t. sk1[]=sk1'[r[]] *)
       (* we now unify r[?ev1] and ?ev2 *)
       let ev2' = whd_evar i' t2 in
       if isEvar i' ev2' then
         solve_simple_eqn flags (conv_fun evar_conv_x flags) env i'
		          (position_problem false pbty,destEvar i' ev2',Stack.zip i' (term1,r))
       else
         evar_eqappr_x flags env evd pbty
		       ((ev2', sk1), csts1) ((term2, sk2), csts2)
    | Some ([],r), Success i' ->
       (* Symmetrically *)
       (* We have sk1[] = sk2'[] for some sk2' s.t. sk2[]=sk2'[r[]] *)
       (* we now unify ?ev1 and r[?ev2] *)
       let ev1' = whd_evar i' t1 in
       if isEvar i' ev1' then
         solve_simple_eqn flags (conv_fun evar_conv_x flags) env i'
	                  (position_problem true pbty,destEvar i' ev1',Stack.zip i' (term2,r))
       else evar_eqappr_x flags env evd pbty
		          ((ev1', sk1), csts1) ((term2, sk2), csts2)
    | None, (UnifFailure _ as x) ->
       (* sk1 and sk2 have no common outer part *)
       if flexrigid then x else
       if Stack.not_purely_applicative sk2 then
         (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
         flex_rigid true (destEvar evd t1) appr1 appr2
       else
         if Stack.not_purely_applicative sk1 then
           (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
           flex_rigid false (destEvar evd t2) appr2 appr1
         else
           (* We could instead try Miller unification, then
              postpone to see if other equations help, as in:
              [Check fun a b : unit => (eqᵣefl : _ a = _ a b)] *)
           x
    | Some _, Success _ ->
       if flexrigid then UnifFailure (i, NotSameArgSize) else
       (* sk1 and sk2 have a common outer part *)
       if Stack.not_purely_applicative sk2 then
         (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
         flex_rigid true (destEvar evd t1) appr1 appr2
       else
         if Stack.not_purely_applicative sk1 then
           (* Ad hoc compatibility with 8.4 which treated non-app as rigid *)
           flex_rigid false (destEvar evd t2) appr2 appr1
         else
           (* We could instead try Miller unification, then
              postpone to see if other equations help, as in:
              [Check fun a b c : unit => (eqᵣefl : _ a b = _ c a b)] *)
           UnifFailure (i,NotSameArgSize)
    | _, _ -> anomaly (Pp.str "Unexpected result from ise_stack2.")
  and flex_rigid on_left ev (termF, skF as apprF) (termR, skR as apprR) =
    let switch f a b = if on_left then f a b else f b a in
    let eta evd =
      match EConstr.kind evd termR with
      | Lambda _ when (* if ever problem is ill-typed: *) List.is_empty skR ->
         eta env evd false skR termR skF termF
      | Construct u -> eta_constructor flags env evd skR u skF termF
      | _ -> UnifFailure (evd,NotSameHead)
    in
    match Stack.list_of_app_stack skF with
    | None ->
        ise_try evd [consume_stack on_left apprF apprR; eta]
    | Some lF ->
        let tR = Stack.zip evd apprR in
	  miller_pfenning on_left
	    (fun () ->
	      ise_try evd 
	        [eta;(* Postpone the use of an heuristic *)
                 (* (fun i -> first_order true env i termF termR skF skR); *)
		 (fun i -> 
		   if not (occur_rigidly ev i tR) then
                     let i,tF =
                       if isRel i tR || isVar i tR then
                         (* Optimization so as to generate candidates *)
                         let i,ev = evar_absorb_arguments env i ev lF in
                         i,mkEvar ev
                       else
                         i,Stack.zip evd apprF in
		     switch (fun x y -> Success (Evarutil.add_unification_pb (pbty,env,x,y) i))
	               tF tR
		   else
                     UnifFailure (evd,OccurCheck (fst ev,tR)))])
	    ev lF tR evd
  in
  let app_empty = match sk1, sk2 with [], [] -> true | _ -> false in
  (* Evar must be undefined since we have flushed evars *)
  let () = if !debug_unification then
	     let open Pp in
	     Feedback.msg_notice (v 0 (pr_state appr1 ++ cut () ++ pr_state appr2 ++ cut ()) 
		 ++ fnl ()) in
  match (flex_kind_of_term flags env evd term1 sk1,
	 flex_kind_of_term flags env evd term2 sk2) with
    | Flexible (sp1,al1), Flexible (sp2,al2) ->
        (* sk1[?ev1] =? sk2[?ev2] *)
	let f1 i = first_order false env i term1 term2 sk1 sk2
	and f2 i =
          if Evar.equal sp1 sp2 then
	    match ise_stack2 false env i (evar_conv_x flags) sk1 sk2 with
	    |None, Success i' ->
              Success (solve_refl flags (fun p env i pbty a1 a2 ->
                let flags = if p then default_flags env else flags in
                is_success (evar_conv_x flags env i pbty a1 a2))
                env i' (position_problem true pbty) sp1 al1 al2)
	    |_, (UnifFailure _ as x) -> x
            |Some _, _ -> UnifFailure (i,NotSameArgSize)
          else UnifFailure (i,NotSameHead)
        and f3 i = miller true (sp1,al1) appr1 appr2 i
        and f4 i = miller false (sp2,al2) appr2 appr1 i
        and f5 i = consume true appr1 appr2 i in
	ise_try evd [f1; f2; f3; f4; f5]

    | Flexible ev1, MaybeFlexible v2 ->
      flex_maybeflex true ev1 (appr1,csts1) (appr2,csts2) v2

    | MaybeFlexible v1, Flexible ev2 -> 
      flex_maybeflex false ev2 (appr2,csts2) (appr1,csts1) v1

    | MaybeFlexible v1, MaybeFlexible v2 -> begin
        match EConstr.kind evd term1, EConstr.kind evd term2 with
        | LetIn (na1,b1,t1,c'1), LetIn (na2,b2,t2,c'2) ->
        let f1 i = (* FO *)
          ise_and i
            [(fun i -> ise_try i
               [(fun i -> evar_conv_x flags env i CUMUL t1 t2);
                (fun i -> evar_conv_x flags env i CUMUL t2 t1)]);
             (fun i -> evar_conv_x flags env i CONV b1 b2);
	     (fun i ->
	       let b = nf_evar i b1 in
	       let t = nf_evar i t1 in
               let na = Nameops.Name.pick na1 na2 in
	       evar_conv_x flags (push_rel (RelDecl.LocalDef (na,b,t)) env) i pbty c'1 c'2);
	     (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
	and f2 i =
          let out1 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i csts1 (v1,sk1)
          and out2 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i csts2 (v2,sk2)
	  in evar_eqappr_x flags env i pbty out1 out2
	in
	ise_try evd [f1; f2]

	| Proj (p, c), Proj (p', c') 
	  when Constant.equal (Projection.constant p) (Projection.constant p') ->
	  let f1 i = 
	    ise_and i 
	    [(fun i -> evar_conv_x flags env i CONV c c');
	     (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
	  and f2 i =
            let out1 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i csts1 (v1,sk1)
            and out2 = whd_betaiota_deltazeta_for_iota_state flags.open_ts env i csts2 (v2,sk2)
	    in evar_eqappr_x flags env i pbty out1 out2
	  in
	    ise_try evd [f1; f2]
	      
	(* Catch the p.c ~= p c' cases *)
	| Proj (p,c), Const (p',u) when eq_constant (Projection.constant p) p' ->
	  let res = 
	    try Some (destApp evd (Retyping.expand_projection env evd p c []))
	    with Retyping.RetypeError _ -> None
	  in
	    (match res with 
	    | Some (f1,args1) -> 
              evar_eqappr_x flags env evd pbty ((f1,Stack.append_app args1 sk1),csts1)
		(appr2,csts2)
	    | None -> UnifFailure (evd,NotSameHead))
	      
	| Const (p,u), Proj (p',c') when eq_constant p (Projection.constant p') ->
	  let res = 
	    try Some (destApp evd (Retyping.expand_projection env evd p' c' []))
	    with Retyping.RetypeError _ -> None
	  in 
	    (match res with
	    | Some (f2,args2) ->
	      evar_eqappr_x flags env evd pbty (appr1,csts1) ((f2,Stack.append_app args2 sk2),csts2)
	    | None -> UnifFailure (evd,NotSameHead))
	      
	| _, _ ->
	let f1 i = 
	  (* Gather the universe constraints that would make term1 and term2 equal.
	     If these only involve unifications of flexible universes to other universes,
	     allow this identification (first-order unification of universes). Otherwise
	     fallback to unfolding.
	  *)
	  let univs = EConstr.eq_constr_universes evd term1 term2 in
          match univs with
          | Some univs ->
	      ise_and i [(fun i -> 
		try Success (Evd.add_universe_constraints i univs)
		with UniversesDiffer -> UnifFailure (i,NotSameHead)
		| Univ.UniverseInconsistency p -> UnifFailure (i, UnifUnivInconsistency p));
			 (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
          | None ->
            UnifFailure (i,NotSameHead)
	and f2 i =
	  (try 
	     if not flags.with_cs then raise Not_found
	     else conv_record flags env i
               (try check_conv_record env i appr1 appr2
		with Not_found -> check_conv_record env i appr2 appr1)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
	and f3 i =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) or the second argument is potentially
             usable as a canonical projection or canonical value *)
          let rec is_unnamed (hd, args) = match EConstr.kind i hd with
            | (Var _|Construct _|Ind _|Const _|Prod _|Sort _) ->
	      Stack.not_purely_applicative args
            | (CoFix _|Meta _|Rel _)-> true
            | Evar _ -> Stack.not_purely_applicative args
	    (* false (* immediate solution without Canon Struct *)*)
            | Lambda _ -> assert (match args with [] -> true | _ -> false); true
            | LetIn (_,b,_,c) -> is_unnamed
	     (fst (whd_betaiota_deltazeta_for_iota_state
		      flags.open_ts env i Cst_stack.empty (subst1 b c, args)))
	    | Fix _ -> true (* Partially applied fix can be the result of a whd call *)
	    | Proj (p, _) -> Projection.unfolded p || Stack.not_purely_applicative args
            | Case _ | App _| Cast _ -> assert false in
          let rhs_is_stuck_and_unnamed () =
	    let applicative_stack = fst (Stack.strip_app sk2) in
	    is_unnamed
	      (fst (whd_betaiota_deltazeta_for_iota_state
		      flags.open_ts env i Cst_stack.empty (v2, applicative_stack))) in
          let rhs_is_already_stuck =
            rhs_is_already_stuck || rhs_is_stuck_and_unnamed () in

	  if (EConstr.isLambda i term1 || rhs_is_already_stuck)
	    && (not (Stack.not_purely_applicative sk1)) then
	    evar_eqappr_x ~rhs_is_already_stuck flags env i pbty
	      (whd_betaiota_deltazeta_for_iota_state
		 flags.open_ts env i (Cst_stack.add_cst term1 csts1) (v1,sk1))
	      (appr2,csts2)
	  else
	    evar_eqappr_x flags env i pbty (appr1,csts1)
	      (whd_betaiota_deltazeta_for_iota_state
		 flags.open_ts env i (Cst_stack.add_cst term2 csts2) (v2,sk2))
	in
	ise_try evd [f1; f2; f3]
    end

    | Rigid, Rigid when EConstr.isLambda evd term1 && EConstr.isLambda evd term2 ->
        let (na1,c1,c'1) = EConstr.destLambda evd term1 in
        let (na2,c2,c'2) = EConstr.destLambda evd term2 in
        ise_and evd
          [(fun i -> evar_conv_x flags env i CONV c1 c2);
           (fun i ->
	     let c = nf_evar i c1 in
             let na = Nameops.Name.pick na1 na2 in
	     evar_conv_x flags (push_rel (RelDecl.LocalAssum (na,c)) env) i CONV c'1 c'2);
           (** When in modulo_betaiota = false case, lambda's are not reduced *)
           (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]

    | Flexible ev1, Rigid -> flex_rigid true ev1 appr1 appr2
    | Rigid, Flexible ev2 -> flex_rigid false ev2 appr2 appr1

    | MaybeFlexible v1, Rigid ->
	let f3 i =
	  (try 
	     if not flags.with_cs then raise Not_found
	     else conv_record flags env i (check_conv_record env i appr1 appr2)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
	and f4 i =
	  evar_eqappr_x flags env i pbty
	    (whd_betaiota_deltazeta_for_iota_state
	       flags.open_ts env i (Cst_stack.add_cst term1 csts1) (v1,sk1))
	    (appr2,csts2)
	in
	  ise_try evd [f3; f4]

    | Rigid, MaybeFlexible v2 ->
	let f3 i =
	  (try
	     if not flags.with_cs then raise Not_found
	     else conv_record flags env i (check_conv_record env i appr2 appr1)
           with Not_found -> UnifFailure (i,NoCanonicalStructure))
	and f4 i =
	  evar_eqappr_x flags env i pbty (appr1,csts1)
	    (whd_betaiota_deltazeta_for_iota_state
	       flags.open_ts env i (Cst_stack.add_cst term2 csts2) (v2,sk2))
	in
	  ise_try evd [f3; f4]

    (* Eta-expansion *)
    | Rigid, _ when isLambda evd term1 && (* if ever ill-typed: *) List.is_empty sk1 ->
        eta env evd true sk1 term1 sk2 term2

    | _, Rigid when isLambda evd term2 && (* if ever ill-typed: *) List.is_empty sk2 ->
        eta env evd false sk2 term2 sk1 term1

    | Rigid, Rigid -> begin
        match EConstr.kind evd term1, EConstr.kind evd term2 with

	| Sort s1, Sort s2 when app_empty ->
	    (try
              let s1 = ESorts.kind evd s1 in
              let s2 = ESorts.kind evd s2 in
	       let evd' =
		 if pbty == CONV
		 then Evd.set_eq_sort env evd s1 s2
		 else Evd.set_leq_sort env evd s1 s2
	       in Success evd'
	     with Univ.UniverseInconsistency p ->
               UnifFailure (evd,UnifUnivInconsistency p)
	     | e when CErrors.noncritical e -> UnifFailure (evd,NotSameHead))

	| Prod (n1,c1,c'1), Prod (n2,c2,c'2) when app_empty ->
            ise_and evd
              [(fun i -> evar_conv_x flags env i CONV c1 c2);
               (fun i ->
 	         let c = nf_evar i c1 in
                 let na = Nameops.Name.pick n1 n2 in
	         evar_conv_x flags (push_rel (RelDecl.LocalAssum (na,c)) env) i pbty c'1 c'2)]

	| Rel x1, Rel x2 ->
	    if Int.equal x1 x2 then
              exact_ise_stack2 env evd (evar_conv_x flags) sk1 sk2
            else UnifFailure (evd,NotSameHead)

	| Var var1, Var var2 ->
	    if Id.equal var1 var2 then
              exact_ise_stack2 env evd (evar_conv_x flags) sk1 sk2
            else UnifFailure (evd,NotSameHead)

	| Const _, Const _
	| Ind _, Ind _ 
	| Construct _, Construct _ ->
	   rigids env evd sk1 term1 sk2 term2

        | Evar (sp1,al1), Evar (sp2,al2) -> (** Frozen evars *)
          if Evar.equal sp1 sp2 then
	    match ise_stack2 false env evd (evar_conv_x flags) sk1 sk2 with
	    |None, Success i' ->
              (** FIXME: solve_refl can restrict the evar, do we want to allow that? *)
              Success (solve_refl flags (fun p env i pbty a1 a2 ->
                let flags = if p then default_flags env else flags in
                is_success (evar_conv_x flags env i pbty a1 a2))
                env i' (position_problem true pbty) sp1 al1 al2)
	    |_, (UnifFailure _ as x) -> x
            |Some _, _ -> UnifFailure (evd,NotSameArgSize)
          else UnifFailure (evd,NotSameHead)

	| Construct u, _ ->
	  eta_constructor flags env evd sk1 u sk2 term2
	    
	| _, Construct u ->
	  eta_constructor flags env evd sk2 u sk1 term1

	| Fix ((li1, i1),(_,tys1,bds1 as recdef1)), Fix ((li2, i2),(_,tys2,bds2)) -> (* Partially applied fixs *)
	  if Int.equal i1 i2 && Array.equal Int.equal li1 li2 then
            ise_and evd [
	      (fun i -> ise_array2 i (fun i' -> evar_conv_x flags env i' CONV) tys1 tys2);
	      (fun i -> ise_array2 i (fun i' -> evar_conv_x flags (push_rec_types recdef1 env) i' CONV) bds1 bds2);
	      (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2)]
	  else UnifFailure (evd, NotSameHead)

	| CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
            if Int.equal i1 i2  then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x flags env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x flags (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
                 (fun i -> exact_ise_stack2 env i
                     (evar_conv_x flags) sk1 sk2)]
            else UnifFailure (evd,NotSameHead)

	| (Meta _, _) | (_, Meta _) ->
	  begin match ise_stack2 true env evd (evar_conv_x flags) sk1 sk2 with
	  |_, (UnifFailure _ as x) -> x
	  |None, Success i' -> evar_conv_x flags env i' CONV term1 term2
	  |Some (sk1',sk2'), Success i' -> evar_conv_x flags env i' CONV (Stack.zip i' (term1,sk1')) (Stack.zip i' (term2,sk2'))
	  end

	| (Ind _ | Sort _ | Prod _ | CoFix _ | Fix _ | Rel _ | Var _ | Const _ | Evar _ | Lambda _), _ ->
	  UnifFailure (evd,NotSameHead)
	| _, (Ind _ | Sort _ | Prod _ | CoFix _ | Fix _ | Rel _ | Var _ | Const _ | Evar _ | Lambda _) ->
	  UnifFailure (evd,NotSameHead)
        | Case _, _ -> UnifFailure (evd,NotSameHead)
        | Proj _, _ -> UnifFailure (evd,NotSameHead)
	| (App _ | Cast _), _ -> assert false
	| LetIn _, _ -> assert false
      end

and conv_record flags env evd (ctx,(h,h2),c,bs,(params,params1),(us,us2),(sk1,sk2),c1,(n,t2)) =
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
	    let test i = evar_conv_x flags env i CUMUL ty (substl ks b) in
	      (i,t2::ks, m-1, test)
	  else
	    let dloc = Loc.tag Evar_kinds.InternalHole in
            let (i', ev) = Evarutil.new_evar env i ~src:dloc (substl ks b) in
	    (i', ev :: ks, m - 1,test))
	(evd,[],List.length bs,fun i -> Success i) bs
    in
    let app = mkApp (c, Array.rev_of_list ks) in
    ise_and evd'
      [(fun i ->
	exact_ise_stack2 env i
          (fun env' i' cpb x1 x -> evar_conv_x flags env' i' cpb x1 (substl ks x))
          params1 params);
       (fun i ->
	 exact_ise_stack2 env i
           (fun env' i' cpb u1 u -> evar_conv_x flags env' i' cpb u1 (substl ks u))
           us2 us);
       (fun i -> evar_conv_x flags env i CONV c1 app);
       (fun i -> exact_ise_stack2 env i (evar_conv_x flags) sk1 sk2);
       test;
       (fun i -> evar_conv_x flags env i CONV h2
	 (fst (decompose_app_vect i (substl ks h))))]
  else UnifFailure(evd,(*dummy*)NotSameHead)

and eta_constructor flags env evd sk1 ((ind, i), u) sk2 term2 =
  let mib = lookup_mind (fst ind) env in
    match mib.Declarations.mind_record with
    | Some (Some (id, projs, pbs)) when mib.Declarations.mind_finite == Decl_kinds.BiFinite -> 
      let pars = mib.Declarations.mind_nparams in
	(try 
	   let l1' = Stack.tail pars sk1 in
	   let l2' = 
	     let term = Stack.zip evd (term2,sk2) in 
	       List.map (fun p -> EConstr.mkProj (Projection.make p false, term)) (Array.to_list projs)
	   in
             exact_ise_stack2 env evd (evar_conv_x { flags with with_cs = false}) l1'
	       (Stack.append_app_list l2' Stack.empty)
         with
	 | Invalid_argument _ ->
	   (* Stack.tail: partially applied constructor *)
	   UnifFailure(evd,NotSameHead))
    | _ -> UnifFailure (evd,NotSameHead)

let evar_conv_x flags = evar_conv_x flags

(* Profiling *)
let evar_conv_x =
  if Flags.profile then
    let evar_conv_xkey = Profile.declare_profile "evar_conv_x" in
      Profile.profile6 evar_conv_xkey evar_conv_x
  else evar_conv_x

let evar_conv_hook_get, evar_conv_hook_set = Hook.make ~default:evar_conv_x ()

let evar_conv_x flags = Hook.get evar_conv_hook_get flags

let set_evar_conv f = Hook.set evar_conv_hook_set f


(* We assume here |l1| <= |l2| *)

let first_order_unification flags env evd (ev1,l1) (term2,l2) =
  let (deb2,rest2) = Array.chop (Array.length l2-Array.length l1) l2 in
  ise_and evd
    (* First compare extra args for better failure message *)
    [(fun i -> ise_array2 i (fun i -> evar_conv_x flags env i CONV) rest2 l1);
    (fun i ->
      (* Then instantiate evar unless already done by unifying args *)
      let t2 = mkApp(term2,deb2) in
      if is_defined i (fst ev1) then
	evar_conv_x flags env i CONV t2 (mkEvar ev1)
      else
        solve_simple_eqn ~choose:true ~imitate_defs:false
                         flags (conv_fun evar_conv_x flags) env i (None,ev1,t2))]

let choose_less_dependent_instance evk evd term args =
  let evi = Evd.find_undefined evd evk in
  let subst = make_pure_subst evi args in
  let subst' = List.filter (fun (id,c) -> EConstr.eq_constr evd c term) subst in
  match subst' with
  | [] -> None
  | (id, _) :: _ -> Some (Evd.define evk (Constr.mkVar id) evd)

(*let apply_on_subterm env evdref f c t =
  let rec applyrec (env,(k,c) as acc) t =
    (* By using eq_constr, we make an approximation, for instance, we *)
    (* could also be interested in finding a term u convertible to t *)
    (* such that c occurs in u *)
    let eq_constr c1 c2 = match EConstr.eq_constr_universes !evdref c1 c2 with
    | None -> false
    | Some cstr ->
      try ignore (Evd.add_universe_constraints !evdref cstr); true
      with UniversesDiffer -> false
    in
    if eq_constr c t then f k
    else
      match EConstr.kind !evdref t with
      | Evar (evk,args) ->
          let ctx = evar_filtered_context (Evd.find_undefined !evdref evk) in
          let g decl a = if is_local_assum decl then applyrec acc a else a in
          mkEvar (evk, Array.of_list (List.map2 g ctx (Array.to_list args)))
      | _ ->
        map_constr_with_binders_left_to_right !evdref
	  (fun d (env,(k,c)) -> (push_rel d env, (k+1,lift 1 c)))
	  applyrec acc t
 *)

type occurrence_match_test =
  env -> evar_map -> constr ->
  env -> evar_map -> int -> constr -> constr -> bool * evar_map

type prefer_abstraction = bool

type occurrence_selection =
  | AtOccurrences of Locus.occurrences
  | Unspecified of prefer_abstraction

type occurrences_selection =
  occurrence_match_test * occurrence_selection list

let default_occurrence_selection = Unspecified false

let default_occurrence_test ~frozen_evars ts _ origsigma _ env sigma _ c pat =
  let flags = { (default_flags_of ~subterm_ts:ts ts) with frozen_evars } in
  match evar_conv_x flags env sigma CONV c pat with
  | Success sigma -> true, sigma
  | UnifFailure _ -> false, sigma

let default_occurrences_selection ?(frozen_evars=Evar.Set.empty) ts n =
  (default_occurrence_test ~frozen_evars ts,
   List.init n (fun _ -> default_occurrence_selection))

let apply_on_subterm env evdref fixedref f test c t =
  let test = test env !evdref c in
  let prc env = print_constr_env env !evdref in
  let rec applyrec (env,(k,c) as acc) t =
    if Evar.Set.exists (fun fixed -> occur_evar !evdref fixed t) !fixedref then
      match EConstr.kind !evdref t with
      | Evar (ev, args) when Evar.Set.mem ev !fixedref -> t
      | _ -> map_constr_with_binders_left_to_right !evdref
	      (fun d (env,(k,c)) -> (push_rel d env, (k+1,lift 1 c)))
	      applyrec acc t
    else
    (if !debug_ho_unification then
     Feedback.msg_debug Pp.(str"Testing " ++ prc env c ++ str" against " ++ prc env t);
     let b, evd =
        try test env !evdref k c t
        with e when CErrors.noncritical e -> assert false in
     if b then (evdref := evd;
                if !debug_ho_unification then Feedback.msg_debug (Pp.str "succeeded");
                f k t)
     else (
       if !debug_ho_unification then Feedback.msg_debug (Pp.str "failed");
       map_constr_with_binders_left_to_right !evdref
        (fun d (env,(k,c)) -> (push_rel d env, (k+1,lift 1 c)))
	applyrec acc t))
  in
  applyrec (env,(0,c)) t

let filter_possible_projections evd c ty ctxt args =
  (* Since args in the types will be replaced by holes, we count the
     fv of args to have a well-typed filter; don't know how necessary
    it is however to have a well-typed filter here *)
  let fv1 = free_rels evd (mkApp (c,args)) (* Hack: locally untyped *) in
  let fv2 = collect_vars evd (mkApp (c,args)) in
  let len = Array.length args in
  let tyvars = collect_vars evd ty in
  List.map_i (fun i decl ->
    let () = assert (i < len) in
    let a = Array.unsafe_get args i in
    (match decl with
     | NamedDecl.LocalAssum _ -> false
     | NamedDecl.LocalDef (_,c,_) -> not (isRel evd (EConstr.of_constr c) || isVar evd (EConstr.of_constr c))) ||
    a == c ||
    (* Here we make an approximation, for instance, we could also be *)
    (* interested in finding a term u convertible to c such that a occurs *)
    (* in u *)
    isRel evd a && Int.Set.mem (destRel evd a) fv1 ||
    isVar evd a && Id.Set.mem (destVar evd a) fv2 ||
    Id.Set.mem (NamedDecl.get_id decl) tyvars)
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

let check_selected_occs env sigma c occ occs =
  let notfound =
    match occs with
    | AtOccurrences occs ->
       (match occs with
       | Locus.AtLeastOneOccurrence -> occ == 1
       | Locus.AllOccurrences -> false
       | Locus.AllOccurrencesBut l -> List.last l > occ
       | Locus.OnlyOccurrences l -> List.last l > occ
       | Locus.NoOccurrences -> false)
    | Unspecified abstract -> false
  in if notfound then
     raise (PretypeError (env,sigma,NoOccurrenceFound (c,None)))
     else ()

exception TypingFailed of evar_map

let set_of_evctx l =
  List.fold_left (fun s decl -> Id.Set.add (NamedDecl.get_id decl) s) Id.Set.empty l

(** Weaken the existentials so that they can be typed in sign and raise
    an error if the term otherwise mentions variables not bound in sign. *)
let thin_evars env sigma sign c =
  let evdref = ref sigma in
  let ctx = set_of_evctx sign in
  let rec applyrec (env,acc) t =
    match kind sigma t with
    | Evar (ev, args) ->
       let evi = Evd.find_undefined sigma ev in
       let filter = Array.map (fun c -> Id.Set.subset (collect_vars sigma c) ctx) args in
       let filter = Filter.make (Array.to_list filter) in
       let candidates = Option.map (List.map EConstr.of_constr) (evar_candidates evi) in
       let evd, ev = restrict_evar !evdref ev filter candidates in
       evdref := evd; whd_evar !evdref t
    | Var id ->
       if not (Id.Set.mem id ctx) then raise (TypingFailed sigma)
       else t
    | _ ->
       map_constr_with_binders_left_to_right !evdref
        (fun d (env,acc) -> (push_rel d env, acc+1))
	applyrec (env,acc) t
  in
  let c' = applyrec (env,0) c in
  (!evdref, c')

let second_order_matching flags env_rhs evd (evk,args) (test,argoccs) rhs =
  try
  let evi = Evd.find_undefined evd evk in
  let evi = nf_evar_info evd evi in
  let env_evar_unf = evar_env evi in
  let env_evar = evar_filtered_env evi in
  let sign = named_context_val env_evar in
  let ctxt = evar_filtered_context evi in
  if !debug_ho_unification then
    (Feedback.msg_debug Pp.(str"env rhs: " ++ print_env env_rhs);
     Feedback.msg_debug Pp.(str"env evars: " ++ print_env env_evar));
  let args = Array.map (nf_evar evd) args in
  let vars = List.map NamedDecl.get_id ctxt in
  let argsubst = List.map2 (fun id c -> (id, c)) vars (Array.to_list args) in
  let instance = List.map mkVar vars in
  let rhs = nf_evar evd rhs in
  if not (noccur_evar env_rhs evd evk rhs) then raise (TypingFailed evd);
  (** Ensure that any progress made by Typing.e_solve_evars will not contradict
      the solution we are trying to build here by adding the problem as a constraint. *)
  let evd = Evarutil.add_unification_pb (CONV,env_rhs,mkEvar (evk,args),rhs) evd in
  let evdref = ref evd in
  let prc env c = print_constr_env env !evdref c in
  let rec make_subst = function
  | decl'::ctxt', c::l, occs::occsl when isVarId evd (NamedDecl.get_id decl') c ->
      begin match occs with
      | AtOccurrences loc when not (Locusops.is_all_occurrences loc) ->
      user_err Pp.(str "Cannot force abstraction on identity instance.")
      | _ ->
        make_subst (ctxt',l,occsl)
      end
  | decl'::ctxt', c::l, occs::occsl ->
      let id = NamedDecl.get_id decl' in
      let t = EConstr.of_constr (NamedDecl.get_type decl') in
      let evs = ref [] in
      let c = nf_evar evd c in
      (* ty is in env_rhs now *)
      let ty = replace_vars argsubst t in
      let filter' = filter_possible_projections !evdref c (nf_evar evd ty) ctxt args in
      (id,t,c,ty,evs,Filter.make filter',occs) :: make_subst (ctxt',l,occsl)
  | _, _, [] -> []
  | _ -> anomaly (Pp.str "Signature or instance are shorter than the occurrences list") in
  let fixed = ref Evar.Set.empty in
  let rec set_holes env_rhs evdref rhs = function
  | (id,idty,c,cty,evsref,filter,occs)::subst ->
     let c = nf_evar !evdref c in
     if !debug_ho_unification then
       Feedback.msg_debug Pp.(str"set holes for: " ++
                                prc env_rhs (mkVar id) ++ spc () ++
                                prc env_rhs c ++ str" in " ++
                                prc env_rhs rhs);
     let occ = ref 1 in
     let set_var k inst =
       let oc = !occ in
       if !debug_ho_unification then
       (Feedback.msg_debug Pp.(str"Found one occurrence");
        Feedback.msg_debug Pp.(str"cty: " ++ prc env_rhs c));
       incr occ;
       match occs with
       | AtOccurrences occs ->
	  if Locusops.is_selected oc occs then mkVar id
	  else inst
       | Unspecified prefer_abstraction ->
          let evty = set_holes env_rhs evdref cty subst in
          let evty = nf_evar !evdref evty in
        if !debug_ho_unification then
          Feedback.msg_debug Pp.(str"abstracting one occurrence " ++ prc env_rhs inst ++
                                   str" of type: " ++ prc env_evar evty ++
                                   str " for " ++ prc env_rhs c);
        let instance = Filter.filter_list filter instance in
        (** Allow any type lower than the variable's type as the
            abstracted subterm might have a smaller type, which could be
            crucial to make the surrounding context typecheck. *)
        let evd, evty =
          if isArity !evdref evty then
            refresh_universes ~status:Evd.univ_flexible (Some true)
                              env_evar_unf !evdref evty
          else !evdref, evty in
        let (evd, ev) = new_evar_instance sign evd evty ~filter instance in
        let evk = fst (destEvar !evdref ev) in
        evdref := evd;
        evsref := (evk,evty,inst,prefer_abstraction)::!evsref;
        fixed := Evar.Set.add evk !fixed;
        ev
     in
     let rhs' = apply_on_subterm env_rhs evdref fixed set_var test c rhs in
     if !debug_ho_unification then
       Feedback.msg_debug Pp.(str"abstracted: " ++ prc env_rhs rhs');
     let () =
       check_selected_occs env_rhs !evdref c !occ occs
     in set_holes (push_named (Context.Named.Declaration.LocalAssum (id,idty)) env_rhs)
                  evdref rhs' subst
  | [] -> rhs in

  let subst = make_subst (ctxt,Array.to_list args,argoccs) in

  let rhs' = set_holes env_rhs evdref rhs subst in
  let evd = !evdref in
  let rhs' = nf_evar evd rhs' in
  (** Thin evars making the term typable in env_evar *)
  let evd, rhs' = thin_evars env_evar evd ctxt rhs' in
  (* We instantiate the evars of which the value is forced by typing *)
  if !debug_ho_unification then
    (Feedback.msg_debug Pp.(str"solve_evars on: " ++ prc env_evar rhs');
     Feedback.msg_debug Pp.(str"evars: " ++ pr_evar_map (Some 0) evd));
  let evd,rhs' =
    let evdref = ref evd in
    try let c = !solve_evars env_evar evdref rhs' in !evdref, c
    with e when Pretype_errors.precatchable_exception e ->
      (* Could not revert all subterms *)
      raise (TypingFailed !evdref) in
  let rhs' = nf_evar evd rhs' in
  (* We instantiate the evars of which the value is forced by typing *)
  if !debug_ho_unification then
    (Feedback.msg_debug Pp.(str"after solve_evars: " ++ prc env_evar rhs');
     Feedback.msg_debug Pp.(str"evars: " ++ pr_evar_map (Some 0) evd));

  let rec abstract_free_holes evd = function
   | (id,idty,c,cty,evsref,_,_)::l ->
     let c = nf_evar evd c in
     if !debug_ho_unification then
       Feedback.msg_debug Pp.(str"abstracting: " ++
                                prc env_rhs (mkVar id) ++ spc () ++
                                prc env_rhs c);
      let rec force_instantiation evd = function
      | (evk,evty,inst,abstract)::evs ->
         let evk = Option.default evk (Evarutil.advance evd evk) in
         let evd =
            if is_undefined evd evk then
              (* We try abstraction or concretisation for *)
              (* this unconstrained occurrence *)
              (* and we use typing to propagate this instantiation *)
              (* We avoid making an arbitrary choice by leaving candidates *)
              (* if both can work *)
              let evi = Evd.find_undefined evd evk in
              let vid = mkVar id in
              let candidates = [inst; vid] in
              try
                let evd, ev = Evarutil.restrict_evar evd evk (Evd.evar_filter evi) (Some candidates) in
                let evi = Evd.find evd ev in
                (match evar_candidates evi with
                 | Some [t] ->
                    if not (noccur_evar env_rhs evd ev (EConstr.of_constr t)) then
                      raise (TypingFailed evd);
                    let evd = Evd.define ev t evd in
                    check_evar_instance evd ev (EConstr.of_constr t) (conv_fun evar_conv_x flags)
                 | Some l when abstract && List.exists (fun c -> isVarId evd id (EConstr.of_constr c)) l ->
                    let evd = Evd.define ev (EConstr.Unsafe.to_constr vid) evd in
                    check_evar_instance evd ev vid (conv_fun evar_conv_x flags)
                 | _ -> evd)
              with e -> user_err (Pp.str "Cannot find an instance")
            else
              ((if !debug_ho_unification then
                  let evi = Evd.find evd evk in
                  let env = Evd.evar_env evi in
                  Feedback.msg_debug Pp.(str"evar is defined: " ++
                     int (Evar.repr evk) ++ spc () ++
                     prc env (match evar_body evi with Evar_defined c -> EConstr.of_constr c
                                                     | Evar_empty -> assert false)));
               evd)
          in
          force_instantiation evd evs
      | [] ->
          abstract_free_holes evd l
      in
      force_instantiation evd !evsref
  | [] ->
     if Evd.is_defined evd evk then
       (** Can happen due to dependencies: instantiating evars in the arguments of evk might 
           instantiate evk itself. *)
       (if !debug_ho_unification then
          begin
            let evi = Evd.find evd evk in
            let evenv = evar_env evi in
            let body = match evar_body evi with Evar_empty -> assert false | Evar_defined c -> c in
            Feedback.msg_debug Pp.(str"evar was defined already as: " ++ prc evenv (EConstr.of_constr body))
          end;
        evd)
     else
       let evd =
         try
           let evi = Evd.find_undefined evd evk in
           let evenv = evar_env evi in
           let evdref = ref evd in
           let rhs' = nf_evar !evdref rhs' in
           if !debug_ho_unification then
             Feedback.msg_debug Pp.(str"abstracted type before second solve_evars: " ++
                                      prc evenv rhs');
           (** solve_evars is not commuting with nf_evar, because restricting
               an evar might provide a more specific type. *)
           let _ = !solve_evars evenv evdref rhs' in
           (* Feedback.msg_debug Pp.(str"evenv: " ++ print_named_context evenv); *)
           if !debug_ho_unification then
             Feedback.msg_debug Pp.(str"abstracted type: " ++ prc evenv (nf_evar !evdref rhs'));
           Evarsolve.check_evar_instance !evdref evk rhs'
                                         (conv_fun evar_conv_x (default_flags_of full_transparent_state))
         with IllTypedInstance _ -> raise (TypingFailed evd)
       in
      Evd.define evk (EConstr.Unsafe.to_constr rhs') evd 
  in
  let evd = abstract_free_holes evd subst in
  evd, true
  with TypingFailed evd -> evd, false

let default_evar_selection flags evd (ev,args) =
  let evi = Evd.find_undefined evd ev in
  let rec aux args abs =
    match args, abs with
    | _ :: args, a :: abs ->
       let spec = if not flags.allow_K_at_toplevel then
                    AtOccurrences (if a then Locus.AtLeastOneOccurrence else Locus.AllOccurrences)
                  else Unspecified a in
       spec :: aux args abs
    | l, [] -> List.map (fun _ -> default_occurrence_selection) l
    | [], _ :: _ -> assert false
  in aux (Array.to_list args) evi.evar_abstraction

let second_order_matching_with_args flags env evd with_ho pbty ev l t =
  if with_ho then
    let evd,ev = evar_absorb_arguments env evd ev (Array.to_list l) in
    let argoccs = default_evar_selection flags evd ev in
    let test = default_occurrence_test ~frozen_evars:flags.frozen_evars flags.subterm_ts in
    let evd, b =
      try second_order_matching flags env evd ev (test,argoccs) t
      with PretypeError (_, _, NoOccurrenceFound _) -> evd, false
    in
    if b then Success evd
    else
      UnifFailure (evd, ConversionFailed (env,mkApp(mkEvar ev,l),t))
  else
    let pb = to_pb (pbty,env,mkApp(mkEvar ev,l),t) in
    UnifFailure (evd, CannotSolveConstraint (pb,ProblemBeyondCapabilities))

let is_beyond_capabilities = function
  | CannotSolveConstraint (pb,ProblemBeyondCapabilities) -> true
  | _ -> false

(* TODO frozen *)
let apply_conversion_problem_heuristic flags env evd with_ho pbty t1 t2 =
  let t1 = apprec_nohdbeta flags env evd (whd_head_evar evd t1) in
  let t2 = apprec_nohdbeta flags env evd (whd_head_evar evd t2) in
  let (term1,l1 as appr1) = try destApp evd t1 with DestKO -> (t1, [||]) in
  let (term2,l2 as appr2) = try destApp evd t2 with DestKO -> (t2, [||]) in
  let () = if !debug_unification then
	     let open Pp in
	     Feedback.msg_notice (v 0 (str "Heuristic:" ++ spc () ++ print_constr t1
                                       ++ cut () ++ print_constr t2 ++ cut ())) in
  let app_empty = Array.is_empty l1 && Array.is_empty l2 in
  match EConstr.kind evd term1, EConstr.kind evd term2 with
  | Evar (evk1,args1), (Rel _|Var _) when app_empty
      && List.for_all (fun a -> EConstr.eq_constr evd a term2 || isEvar evd a)
        (remove_instance_local_defs evd evk1 args1) ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      (match choose_less_dependent_instance evk1 evd term2 args1 with
      | Some evd -> Success evd
      | None ->
         let reason = ProblemBeyondCapabilities in
         UnifFailure (evd, CannotSolveConstraint (to_pb (pbty,env,t1,t2),reason)))
  | (Rel _|Var _), Evar (evk2,args2) when app_empty
      && List.for_all (fun a -> EConstr.eq_constr evd a term1 || isEvar evd a)
        (remove_instance_local_defs evd evk2 args2) ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      (match choose_less_dependent_instance evk2 evd term1 args2 with
      | Some evd -> Success evd
      | None ->
         let reason = ProblemBeyondCapabilities in
         UnifFailure (evd, CannotSolveConstraint (to_pb (pbty,env,t1,t2),reason)))
  | Evar (evk1,args1), Evar (evk2,args2) when Evar.equal evk1 evk2 ->
     let f ontype env evd pbty x y =
       let reds = if ontype then full_transparent_state else flags.open_ts in
       is_fconv ~reds pbty env evd x y in
      Success (solve_refl ~can_drop:true flags f env evd
                 (position_problem true pbty) evk1 args1 args2)
  | Evar ev1, Evar ev2 when app_empty ->
      Success (solve_evar_evar ~force:true
        flags (evar_define flags (conv_fun evar_conv_x flags) ~choose:true) (conv_fun evar_conv_x flags) env evd
        (position_problem true pbty) ev1 ev2)
  | Evar ev1,_ when Array.length l1 <= Array.length l2 ->
      (* On "?n t1 .. tn = u u1 .. u(n+p)", try first-order unification *)
      (* and otherwise second-order matching *)
      ise_try evd
        [(fun evd -> first_order_unification flags env evd (ev1,l1) appr2);
         (fun evd ->
           second_order_matching_with_args flags env evd with_ho pbty ev1 l1 t2)]
  | _,Evar ev2 when Array.length l2 <= Array.length l1 ->
      (* On "u u1 .. u(n+p) = ?n t1 .. tn", try first-order unification *)
      (* and otherwise second-order matching *)
      ise_try evd
        [(fun evd -> first_order_unification flags env evd (ev2,l2) appr1);
         (fun evd ->
           second_order_matching_with_args flags env evd with_ho pbty ev2 l2 t1)]
  | Evar ev1,_ ->
      (* Try second-order pattern-matching *)
      second_order_matching_with_args flags env evd with_ho pbty ev1 l1 t2
  | _,Evar ev2 ->
      (* Try second-order pattern-matching *)
      second_order_matching_with_args flags env evd with_ho pbty ev2 l2 t1
  | _ ->
      (* Some head evar have been instantiated, or unknown kind of problem *)
      evar_conv_x flags env evd pbty t1 t2

let error_cannot_unify env evd pb ?reason t1 t2 =
  Pretype_errors.error_cannot_unify
    ?loc:(loc_of_conv_pb evd pb) env
    evd ?reason (t1, t2)

let check_problems_are_solved env evd =
  match snd (extract_all_conv_pbs evd) with
  | (pbty,env,t1,t2) as pb::_ -> error_cannot_unify env evd pb (EConstr.of_constr t1) (EConstr.of_constr t2)
  | _ -> ()

exception MaxUndefined of (Evar.t * evar_info * Constr.t list)

let max_undefined_with_candidates evd =
  let fold evk evi () = match evi.evar_candidates with
  | None -> ()
  | Some l -> raise (MaxUndefined (evk, evi, l))
  in
  (** [fold_right] traverses the undefined map in decreasing order of indices.
  The evar with candidates of maximum index is thus the first evar with
  candidates found by a [fold_right] traversal. This has a significant impact on
  performance. *)
  try
    let () = Evar.Map.fold_right fold (Evd.undefined_map evd) () in
    None
  with MaxUndefined ans ->
    Some ans

let rec solve_unconstrained_evars_with_candidates flags evd =
  (* max_undefined is supposed to return the most recent, hence
     possibly most dependent evar *)
  match max_undefined_with_candidates evd with
  | None -> evd
  | Some (evk,ev_info,l) ->
      let rec aux = function
      | [] -> user_err Pp.(str "Unsolvable existential variables.")
      | a::l ->
          try
            let conv_algo = conv_fun evar_conv_x flags in
            let evd = check_evar_instance evd evk (EConstr.of_constr a) conv_algo in
            let evd = Evd.define evk a evd in
            match reconsider_unif_constraints conv_algo evd with
            | Success evd -> solve_unconstrained_evars_with_candidates flags evd
            | UnifFailure _ -> aux l
          with
          | IllTypedInstance _ -> aux l
          | e when Pretype_errors.precatchable_exception e -> aux l in
      (* List.rev is there to favor most dependent solutions *)
      (* and favor progress when used with the refine tactics *)
      let evd = aux (List.rev l) in
      solve_unconstrained_evars_with_candidates flags evd

let solve_unconstrained_impossible_cases env evd =
  Evd.fold_undefined (fun evk ev_info evd' ->
    match ev_info.evar_source with
    | loc,Evar_kinds.ImpossibleCase ->
      let j, ctx = coq_unit_judge () in
      let evd' = Evd.merge_context_set Evd.univ_flexible_alg ?loc evd' ctx in
      let ty = j_type j in
      let conv_algo = conv_fun evar_conv_x (default_flags env) in
      let evd' = check_evar_instance evd' evk ty conv_algo in
	Evd.define evk (EConstr.Unsafe.to_constr ty) evd' 
    | _ -> evd') evd evd

let solve_unif_constraints_with_heuristics env
    ?(flags=default_flags env) ?(with_ho=false) evd =
  let evd = solve_unconstrained_evars_with_candidates flags evd in
  let rec aux evd pbs progress stuck =
    match pbs with
    | (pbty,env,t1,t2 as pb) :: pbs ->
        let t1 = EConstr.of_constr t1 in
        let t2 = EConstr.of_constr t2 in
        (match apply_conversion_problem_heuristic flags env evd with_ho pbty t1 t2 with
	| Success evd' ->
           let evd' = solve_unconstrained_evars_with_candidates flags evd' in
	   let (evd', rest) = extract_all_conv_pbs evd' in
           begin match rest with
            | [] -> aux evd' pbs true stuck
            | l ->
               (* Unification got actually stuck, postpone *)
               let reason = CannotSolveConstraint (pb,ProblemBeyondCapabilities) in
	       aux evd pbs progress ((pb, reason):: stuck)
            end
        | UnifFailure (evd,reason) ->
           if is_beyond_capabilities reason then
             aux evd pbs progress ((pb,reason) :: stuck)
           else aux evd [] false ((pb,reason) :: stuck))
    | _ -> 
	if progress then aux evd (List.map fst stuck) false []
	else 
	  match stuck with
	  | [] -> (* We're finished *) evd
	  | ((pbty,env,t1,t2 as pb), reason) :: _ ->
	      (* There remains stuck problems *)
            let t1 = EConstr.of_constr t1 in
            let t2 = EConstr.of_constr t2 in
	      Pretype_errors.error_cannot_unify ?loc:(loc_of_conv_pb evd pb)
                env evd ~reason (t1, t2)
  in
  let (evd,pbs) = extract_all_conv_pbs evd in
  let heuristic_solved_evd = aux evd pbs false [] in
  check_problems_are_solved env heuristic_solved_evd;
  solve_unconstrained_impossible_cases env heuristic_solved_evd

let consider_remaining_unif_problems = solve_unif_constraints_with_heuristics

(* Main entry points *)

exception UnableToUnify of evar_map * unification_error

let the_conv_x env ?(ts=default_transparent_state env) t1 t2 evd =
  let flags = default_flags_of ts in
  match evar_conv_x flags env evd CONV  t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let the_conv_x_leq env ?(ts=default_transparent_state env) t1 t2 evd =
  let flags = default_flags_of ts in
  match evar_conv_x flags env evd CUMUL t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let e_conv env ?(ts=default_transparent_state env) evdref t1 t2 =
  let flags = default_flags_of ts in
  match evar_conv_x flags env !evdref CONV t1 t2 with
  | Success evd' -> evdref := evd'; true
  | _ -> false

let e_cumul env ?(ts=default_transparent_state env) evdref t1 t2 =
  let flags = default_flags_of ts in
  match evar_conv_x flags env !evdref CUMUL t1 t2 with
  | Success evd' -> evdref := evd'; true
  | _ -> false

let unify flags env evd t1 t2 =
  match evar_conv_x flags env evd CONV t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let unify_leq flags env evd t1 t2 =
  match evar_conv_x flags env evd CUMUL t1 t2 with
  | Success evd' -> evd'
  | UnifFailure (evd',e) -> raise (UnableToUnify (evd',e))

let unify_with_heuristics flags ~with_ho env evd cv_pb ty1 ty2 =
  let res = evar_conv_x flags env evd cv_pb ty1 ty2 in
  match res with
  | Success evd ->
     solve_unif_constraints_with_heuristics ~flags ~with_ho env evd
  | UnifFailure (evd, reason) ->
     raise (PretypeError (env, evd, CannotUnify (ty1, ty2, Some reason)))
