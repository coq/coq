(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Closure
open Reduction
open Reductionops
open Termops
open Environ
open Typing
open Classops
open Recordops 
open Evarutil
open Libnames
open Evd

type flex_kind_of_term =
  | Rigid of constr 
  | MaybeFlexible of constr
  | Flexible of existential

let flex_kind_of_term c l =
  match kind_of_term c with
    | Const _ -> MaybeFlexible c
    | Rel n -> MaybeFlexible c
    | Var id -> MaybeFlexible c
    | Lambda _ when l<>[] -> MaybeFlexible c
    | LetIn _  -> MaybeFlexible c
    | Evar ev -> Flexible ev
    | _ -> Rigid c

let eval_flexible_term env c =
  match kind_of_term c with
  | Const c -> constant_opt_value env c
  | Rel n ->
      (try let (_,v,_) = lookup_rel n env in Option.map (lift n) v
      with Not_found -> None)
  | Var id ->
      (try let (_,v,_) = lookup_named id env in v with Not_found -> None)
  | LetIn (_,b,_,c) -> Some (subst1 b c)
  | Lambda _ -> Some c
  | _ -> assert false

let evar_apprec env evd stack c =
  let sigma = evars_of evd in
  let rec aux s =
    let (t,stack) = whd_betaiota_deltazeta_for_iota_state env sigma s in
    match kind_of_term t with
      | Evar (evk,_ as ev) when Evd.is_defined sigma evk ->
	  aux (Evd.existential_value sigma ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack_list stack empty_stack)

let apprec_nohdbeta env evd c =
  match kind_of_term (fst (Reductionops.whd_stack c)) with
    | (Case _ | Fix _) -> applist (evar_apprec env evd [] c)
    | _ -> c

(* [check_conv_record (t1,l1) (t2,l2)] tries to decompose the problem
   (t1 l1) = (t2 l2) into a problem

     l1 = params1@c1::extra_args1
     l2 = us2@extra_args2
     (t1 params1 c1) = (proji params (c xs))
     (t2 us2) = (cstr us)
     extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (cstr us), for which we know that the i-th projection proji
   satisfies

      (proji params (c xs)) = (cstr us)

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record (t1,l1) (t2,l2) =
  try
    let proji = global_of_constr t1 in
    let canon_s,l2_effective = 
      try
	match kind_of_term t2 with
	    Prod (_,a,b) -> (* assert (l2=[]); *)
      	      if dependent (mkRel 1) b then raise Not_found
	      else lookup_canonical_conversion (proji, Prod_cs),[a;pop b]
	  | Sort s -> 
	      lookup_canonical_conversion 
		(proji, Sort_cs (family_of_sort s)),[]
	  | _ -> 
	      let c2 = global_of_constr t2 in
		lookup_canonical_conversion (proji, Const_cs c2),l2
      with Not_found -> 
	lookup_canonical_conversion (proji,Default_cs),[]
    in
    let { o_DEF = c; o_INJ=n; o_TABS = bs; o_TPARAMS = params; o_TCOMPS = us } 
	= canon_s in
    let params1, c1, extra_args1 =
      match list_chop (List.length params) l1 with 
	| params1, c1::extra_args1 -> params1, c1, extra_args1
	| _ -> raise Not_found in
    let us2,extra_args2 = list_chop (List.length us) l2_effective in
    c,bs,(params,params1),(us,us2),(extra_args1,extra_args2),c1,
    (n,applist(t2,l2))
  with Failure _ | Not_found -> 
    raise Not_found

(* Precondition: one of the terms of the pb is an uninstantiated evar,
 * possibly applied to arguments. *)

let rec ise_try evd = function
    [] -> assert false
  | [f] -> f evd
  | f1::l ->
      let (evd',b) = f1 evd in
      if b then (evd',b) else ise_try evd l

let ise_and evd l =
  let rec ise_and i = function
      [] -> assert false
    | [f] -> f i
    | f1::l ->
        let (i',b) = f1 i in
        if b then  ise_and i' l else (evd,false) in
  ise_and evd l

let ise_list2 evd f l1 l2 =
  let rec ise_list2 i l1 l2 =
    match l1,l2 with
        [], [] -> (i, true)
      | [x], [y] -> f i x y
      | x::l1, y::l2 ->
          let (i',b) = f i x y in
          if b then ise_list2 i' l1 l2 else (evd,false)
      | _ -> (evd, false) in
  ise_list2 evd l1 l2

let ise_array2 evd f v1 v2 =
  let rec allrec i = function
    | -1 -> (i,true)
    | n ->
        let (i',b) = f i v1.(n) v2.(n) in
        if b then allrec i' (n-1) else (evd,false)
  in 
  let lv1 = Array.length v1 in
  if lv1 = Array.length v2 then allrec evd (pred lv1) 
  else (evd,false)

let rec evar_conv_x env evd pbty term1 term2 = 
  let sigma = evars_of evd in
  let term1 = whd_castappevar sigma term1 in
  let term2 = whd_castappevar sigma term2 in
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]
     could have found, we do it only if the terms are free of evar.
     Note: incomplete heuristic... *)
  if is_ground_term evd term1 && is_ground_term evd term2 &
     is_fconv pbty env (evars_of evd) term1 term2
  then
    (evd,true)
  else
  let term1 = apprec_nohdbeta env evd term1 in
  let term2 = apprec_nohdbeta env evd term2 in
  if is_undefined_evar evd term1 then
    solve_simple_eqn evar_conv_x env evd (pbty,destEvar term1,term2)
  else if is_undefined_evar evd term2 then
    solve_simple_eqn evar_conv_x env evd (pbty,destEvar term2,term1)
  else
    evar_eqappr_x env evd pbty (decompose_app term1) (decompose_app term2)

and evar_eqappr_x env evd pbty (term1,l1 as appr1) (term2,l2 as appr2) =
  (* Evar must be undefined since we have whd_ised *)
  match (flex_kind_of_term term1 l1, flex_kind_of_term term2 l2) with
    | Flexible (sp1,al1 as ev1), Flexible (sp2,al2 as ev2) ->
	let f1 i =
	  if List.length l1 > List.length l2 then 
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            ise_and i
              [(fun i -> solve_simple_eqn evar_conv_x env i
	        (pbty,ev2,applist(term1,deb1)));
              (fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) rest1 l2)]
	  else
	    let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
            ise_and i
              [(fun i -> solve_simple_eqn evar_conv_x env i
	          (pbty,ev1,applist(term2,deb2)));
              (fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) l1 rest2)]
	and f2 i =
          if sp1 = sp2 then
            ise_and i
            [(fun i -> ise_list2 i 
                  (fun i -> evar_conv_x env i CONV) l1 l2);
             (fun i -> solve_refl evar_conv_x env i sp1 al1 al2,
                  true)]
          else (i,false)
	in 
	ise_try evd [f1; f2]

    | Flexible ev1, MaybeFlexible flex2 ->
	let f1 i =
	  if 
	    is_unification_pattern_evar env ev1 l1 & 
	    not (occur_evar (fst ev1) (applist appr2))
	  then
	    (* Miller-Pfenning's patterns unification *)
	    (* Preserve generality (except that CCI has no eta-conversion) *)
	    let t2 = nf_evar (evars_of evd) (applist appr2) in
	    let t2 = solve_pattern_eqn env l1 t2 in
	    solve_simple_eqn evar_conv_x env evd (pbty,ev1,t2)
	  else if
            List.length l1 <= List.length l2
	  then
	    (* Try first-order unification *)
	    (* (heuristic that gives acceptable results in practice) *)
	    let (deb2,rest2) =
              list_chop (List.length l2-List.length l1) l2 in
            ise_and i
              (* First compare extra args for better failure message *)
              [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) l1 rest2);
               (fun i -> evar_conv_x env i pbty term1 (applist(term2,deb2)))]
          else (i,false)
	and f4 i =
	  match eval_flexible_term env flex2 with
	    | Some v2 ->
		evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
	    | None -> (i,false)
	in 
	ise_try evd [f1; f4]

    | MaybeFlexible flex1, Flexible ev2 ->
	let f1 i =
	  if 
	    is_unification_pattern_evar env ev2 l2 & 
	    not (occur_evar (fst ev2) (applist appr1))
	  then
	    (* Miller-Pfenning's patterns unification *)
	    (* Preserve generality (except that CCI has no eta-conversion) *)
	    let t1 = nf_evar (evars_of evd) (applist appr1) in
	    let t1 = solve_pattern_eqn env l2 t1 in
	    solve_simple_eqn evar_conv_x env evd (pbty,ev2,t1)
	  else if
       	    List.length l2 <= List.length l1
	  then
	    (* Try first-order unification *)
	    (* (heuristic that gives acceptable results in practice) *)
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            ise_and i
            (* First compare extra args for better failure message *)
              [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) rest1 l2);
               (fun i -> evar_conv_x env i pbty (applist(term1,deb1)) term2)]
          else (i,false)
	and f4 i =
	  match eval_flexible_term env flex1 with
	    | Some v1 ->
		evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
	    | None -> (i,false)
	in 
	ise_try evd [f1; f4]

    | MaybeFlexible flex1, MaybeFlexible flex2 ->
	let f1 i =
	  if l1 <> [] && l2 <> [] then
            ise_list2 i (fun i -> evar_conv_x env i CONV)
	      (flex1::l1) (flex2::l2)
	  else
	    (i,false)
	and f2 i =
	  (try conv_record env i
             (try check_conv_record appr1 appr2
	      with Not_found -> check_conv_record appr2 appr1)
           with Not_found -> (i,false))
	and f3 i =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) or the second argument is potentially
             usable as a canonical projection *)
	  if isLambda flex1 or is_canonical_projection flex2 then
	    match eval_flexible_term env flex1 with
	    | Some v1 ->
		evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
	    | None ->
		match eval_flexible_term env flex2 with
		| Some v2 ->
		    evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
		| None -> (i,false)
	  else
	    match eval_flexible_term env flex2 with
	    | Some v2 ->
		evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
	    | None ->
		match eval_flexible_term env flex1 with
		| Some v1 ->
		    evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
		| None -> (i,false)
	in 
	ise_try evd [f1; f2; f3]

    | Flexible ev1, Rigid _ ->
	if 
	  is_unification_pattern_evar env ev1 l1 & 
	  not (occur_evar (fst ev1) (applist appr2))
	then
	  (* Miller-Pfenning's patterns unification *)
	  (* Preserve generality (except that CCI has no eta-conversion) *)
	  let t2 = nf_evar (evars_of evd) (applist appr2) in
	  let t2 = solve_pattern_eqn env l1 t2 in
	  solve_simple_eqn evar_conv_x env evd (pbty,ev1,t2)
	else
	  (* Postpone the use of an heuristic *)
	  add_conv_pb (pbty,env,applist appr1,applist appr2) evd,
	  true

    | Rigid _, Flexible ev2 ->
	if 
	  is_unification_pattern_evar env ev2 l2 & 
	  not (occur_evar (fst ev2) (applist appr1))
	then
	  (* Miller-Pfenning's patterns unification *)
	  (* Preserve generality (except that CCI has no eta-conversion) *)
	  let t1 = nf_evar (evars_of evd) (applist appr1) in
	  let t1 = solve_pattern_eqn env l2 t1 in
	  solve_simple_eqn evar_conv_x env evd (pbty,ev2,t1)
	else
	  (* Postpone the use of an heuristic *)
	  add_conv_pb (pbty,env,applist appr1,applist appr2) evd,
	  true

    | MaybeFlexible flex1, Rigid _ ->
	let f3 i =
	  (try conv_record env i (check_conv_record appr1 appr2)
           with Not_found -> (i,false))
	and f4 i =
	  match eval_flexible_term env flex1 with
	    | Some v1 ->
 		evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
	    | None -> (i,false)
	in 
	ise_try evd [f3; f4]
	     
    | Rigid _ , MaybeFlexible flex2 -> 
	let f3 i = 
	  (try conv_record env i (check_conv_record appr2 appr1)
           with Not_found -> (i,false))
	and f4 i =
	  match eval_flexible_term env flex2 with
	    | Some v2 ->
 		evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
	    | None -> (i,false)
	in 
	ise_try evd [f3; f4]

    | Rigid c1, Rigid c2 -> match kind_of_term c1, kind_of_term c2 with
	  
	| Cast (c1,_,_), _ -> evar_eqappr_x env evd pbty (c1,l1) appr2

	| _, Cast (c2,_,_) -> evar_eqappr_x env evd pbty appr1 (c2,l2)

	| Sort s1, Sort s2 when l1=[] & l2=[] ->
            (evd,base_sort_cmp pbty s1 s2)

	| Lambda (na,c1,c'1), Lambda (_,c2,c'2) when l1=[] & l2=[] -> 
            ise_and evd
              [(fun i -> evar_conv_x env i CONV c1 c2);
               (fun i ->
                 let c = nf_evar (evars_of i) c1 in
                 evar_conv_x (push_rel (na,None,c) env) i CONV c'1 c'2)]

	| LetIn (na,b1,t1,c'1), LetIn (_,b2,_,c'2) ->
	    let f1 i =
              ise_and i
                [(fun i -> evar_conv_x env i CONV b1 b2);
                 (fun i ->
                   let b = nf_evar (evars_of i) b1 in
	           let t = nf_evar (evars_of i) t1 in
                   evar_conv_x (push_rel (na,Some b,t) env) i pbty c'1 c'2);
                 (fun i -> ise_list2 i
                     (fun i -> evar_conv_x env i CONV) l1 l2)]
	    and f2 i =
              let appr1 = evar_apprec env i l1 (subst1 b1 c'1)
              and appr2 = evar_apprec env i l2 (subst1 b2 c'2)
	      in evar_eqappr_x env i pbty appr1 appr2
	    in 
	    ise_try evd [f1; f2]

	| LetIn (_,b1,_,c'1), _ ->(* On fait commuter les args avec le Let *)
	     let appr1 = evar_apprec env evd l1 (subst1 b1 c'1)
             in evar_eqappr_x env evd pbty appr1 appr2

	| _, LetIn (_,b2,_,c'2) ->
	    let appr2 = evar_apprec env evd l2 (subst1 b2 c'2)
            in evar_eqappr_x env evd pbty appr1 appr2

	| Prod (n,c1,c'1), Prod (_,c2,c'2) when l1=[] & l2=[] -> 
            ise_and evd
              [(fun i -> evar_conv_x env i CONV c1 c2);
               (fun i ->
 	         let c = nf_evar (evars_of i) c1 in
	         evar_conv_x (push_rel (n,None,c) env) i pbty c'1 c'2)]

	| Ind sp1, Ind sp2 ->
	    if sp1=sp2 then
              ise_list2 evd (fun i -> evar_conv_x env i CONV) l1 l2
            else (evd, false)

	| Construct sp1, Construct sp2 ->
	    if sp1=sp2 then
              ise_list2 evd (fun i -> evar_conv_x env i CONV) l1 l2
            else (evd, false)

	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
            ise_and evd
              [(fun i -> evar_conv_x env i CONV p1 p2);
               (fun i -> evar_conv_x env i CONV c1 c2);
	       (fun i -> ise_array2 i
                   (fun i -> evar_conv_x env i CONV) cl1 cl2);
               (fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) l1 l2)]

	| Fix (li1,(_,tys1,bds1 as recdef1)), Fix (li2,(_,tys2,bds2)) ->
            if li1=li2 then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
	         (fun i -> ise_list2 i
                     (fun i -> evar_conv_x env i CONV) l1 l2)]
	    else (evd,false)
	| CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
            if i1=i2  then
              ise_and evd
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
                 (fun i -> ise_list2 i
                     (fun i -> evar_conv_x env i CONV) l1 l2)]
            else (evd,false)

	| (Meta _ | Lambda _), _ -> (evd,false)
	| _, (Meta _ | Lambda _) -> (evd,false)

	| (Ind _ | Construct _ | Sort _ | Prod _), _ -> (evd,false)
	| _, (Ind _ | Construct _ | Sort _ | Prod _) -> (evd,false)

	| (App _ | Case _ | Fix _ | CoFix _), 
	  (App _ | Case _ | Fix _ | CoFix _) -> (evd,false)

	| (Rel _ | Var _ | Const _ | Evar _), _ -> assert false
	| _, (Rel _ | Var _ | Const _ | Evar _) -> assert false

and conv_record env evd (c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) = 
  let (evd',ks,_) =
    List.fold_left
      (fun (i,ks,m) b ->
	 if m=0 then (i,t2::ks, n-1) else
	 let dloc = (dummy_loc,InternalHole) in
         let (i',ev) = new_evar i env ~src:dloc (substl ks b) in
	 (i', ev :: ks, n - 1))
      (evd,[],n) bs
  in
  ise_and evd'
    [(fun i ->
      ise_list2 i
        (fun i u1 u -> evar_conv_x env i CONV u1 (substl ks u))
        us2 us);
     (fun i ->
       ise_list2 i
         (fun i x1 x -> evar_conv_x env i CONV x1 (substl ks x))
         params1 params);
     (fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) ts ts1);
     (fun i -> evar_conv_x env i CONV c1 (applist (c,(List.rev ks))))]

(* We assume here |l1| <= |l2| *)

let first_order_unification env evd (ev1,l1) (term2,l2) =
  let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
  ise_and evd
    (* First compare extra args for better failure message *)
    [(fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) rest2 l1);
    (fun i ->
      (* Then instantiate evar unless already done by unifying args *)
      let t2 = applist(term2,deb2) in
      if is_defined_evar i ev1 then
	evar_conv_x env i CONV t2 (mkEvar ev1)
      else
	solve_simple_eqn evar_conv_x env i (CONV,ev1,t2))]

let choose_less_dependent_instance evk evd term args =
  let evi = Evd.find (evars_of evd) evk in
  let subst = make_pure_subst evi args in
  let subst' = List.filter (fun (id,c) -> c = term) subst in
  if subst' = [] then error "Too complex unification problem." else
  Evd.evar_define evk (mkVar (fst (List.hd subst'))) evd

let apply_conversion_problem_heuristic env evd pbty t1 t2 =
  let t1 = apprec_nohdbeta env evd (whd_castappevar (evars_of evd) t1) in
  let t2 = apprec_nohdbeta env evd (whd_castappevar (evars_of evd) t2) in
  let (term1,l1 as appr1) = decompose_app t1 in
  let (term2,l2 as appr2) = decompose_app t2 in
  match kind_of_term term1, kind_of_term term2 with
  | Evar (evk1,args1), (Rel _|Var _) when l1 = [] & l2 = [] ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      assert (array_for_all (fun a -> a = term2 or isEvar a) args1);
      choose_less_dependent_instance evk1 evd term2 args1, true
  | (Rel _|Var _), Evar (evk2,args2) when l1 = [] & l2 = [] ->
      (* The typical kind of constraint coming from pattern-matching return
         type inference *)
      assert (array_for_all ((=) term1) args2);
      choose_less_dependent_instance evk2 evd term1 args2, true
  | Evar ev1,_ when List.length l1 <= List.length l2 ->
      (* On "?n t1 .. tn = u u1 .. u(n+p)", try first-order unification *)
      first_order_unification env evd (ev1,l1) appr2
  | _,Evar ev2 when List.length l2 <= List.length l1 ->
      (* On "u u1 .. u(n+p) = ?n t1 .. tn", try first-order unification *)
      first_order_unification env evd (ev2,l2) appr1
  | _ ->
      (* Some head evar have been instantiated, or unknown kind of problem *)
      evar_conv_x env evd pbty t1 t2

let consider_remaining_unif_problems env evd =
  let (evd,pbs) = extract_all_conv_pbs evd in
  List.fold_left
    (fun (evd,b as p) (pbty,env,t1,t2) ->
      if b then apply_conversion_problem_heuristic env evd pbty t1 t2 else p)
    (evd,true)
    pbs

(* Main entry points *)

let the_conv_x     env t1 t2 evd =
  match evar_conv_x env evd CONV  t1 t2 with
      (evd',true) -> evd'
    | _ -> raise Reduction.NotConvertible

let the_conv_x_leq env t1 t2 evd =
  match evar_conv_x env evd CUMUL t1 t2 with
      (evd', true) -> evd'
    | _ -> raise Reduction.NotConvertible
 
let e_conv env evd t1 t2 =
  match evar_conv_x env !evd CONV t1 t2 with
      (evd',true) -> evd := evd'; true
    | _ -> false

let e_cumul env evd t1 t2 =
  match evar_conv_x env !evd CUMUL t1 t2 with
      (evd',true) -> evd := evd'; true
    | _ -> false
