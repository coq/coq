
(* $Id$ *)

open Pp
open Util
open Names
open Univ
(*i open Generic i*)
open Term
open Declarations
open Sign
open Environ
open Reduction
open Inductive

open Type_errors

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val_only j = j.uj_val

let typed_type_of_judgment env sigma j = j.uj_type

(* This should be a type intended to be assumed *)
let assumption_of_judgment env sigma j =
  match whd_betadeltaiota env sigma (body_of_type j.uj_type) with
    | DOP0(Sort s) -> make_typed j.uj_val s
    | _ -> error_assumption CCI env j.uj_val

(* This should be a type (a priori without intension to be an assumption) *)
let type_judgment env sigma j =
  match whd_betadeltaiota env sigma (body_of_type j.uj_type) with
    | DOP0(Sort s) -> {utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_type CCI env j

let assumption_of_type_judgment j = make_typed j.utj_val j.utj_type

(* Type of a de Bruijn index. *)
	  
let relative env sigma n = 
  try
    let (_,typ) = lookup_rel_type n env in
    { uj_val  = Rel n;
      uj_type = typed_app (lift n) typ }
  with Not_found -> 
    error_unbound_rel CCI env sigma n

(* Management of context of variables. *)

(* Checks if a context of variable is included in another one. *)
(*
let rec hyps_inclusion env sigma sign1 sign2 =
  if sign1 = empty_var_context then true
  else
    let (id1,ty1) = hd_sign sign1 in
    let rec search sign2 =
      if sign2 = empty_var_context then false
      else
	let (id2,ty2) = hd_sign sign2 in
        if id1 = id2 then
	  (is_conv env sigma (body_of_type ty1) (body_of_type ty2))
	  &
	  hyps_inclusion env sigma (tl_sign sign1) (tl_sign sign2)
        else 
	  search (tl_sign sign2)
    in 
    search sign2
*)

(* Checks if the given context of variables [hyps] is included in the
   current context of [env]. *)
(*
let check_hyps id env sigma hyps =
  let hyps' = var_context env in
  if not (hyps_inclusion env sigma hyps hyps') then
    error_reference_variables CCI env id
*)
(* Instantiation of terms on real arguments. *)

let type_of_constant = Instantiate.constant_type

(* Inductive types. *)

(* Q: A faire disparaitre ??
let instantiate_arity mis =
  let ids = ids_of_sign mis.mis_mib.mind_hyps in
  let args = Array.to_list mis.mis_args in 
  let arity = mis.mis_mip.mind_arity in
  { body = instantiate_constr ids arity.body args;
    typ = arity.typ }
*)
let instantiate_arity = mis_typed_arity

let type_of_inductive env sigma i =
  (* TODO: check args *)
  instantiate_arity (lookup_mind_specif i env)

(* Constructors. *)

let type_mconstruct env sigma i mind =
  mis_type_mconstruct i (lookup_mind_specif mind env)

let type_of_constructor env sigma cstr =
  type_mconstruct env sigma
    (index_of_constructor cstr)
    (inductive_of_constructor cstr)

let type_of_existential env sigma c =
  Instantiate.existential_type sigma (destEvar c)

(* Case. *)

let rec mysort_of_arity env sigma c =
  match kind_of_term (whd_betadeltaiota env sigma c) with
    | IsSort s -> s
    | IsProd(_,_,c2) -> mysort_of_arity env sigma c2
    | _ -> invalid_arg "mysort_of_arity"

let error_elim_expln env sigma kp ki =
  if is_info_arity env sigma kp && not (is_info_arity env sigma ki) then
    "non-informative objects may not construct informative ones."
  else 
    match (kind_of_term kp,kind_of_term ki) with 
      | IsSort (Type _), IsSort (Prop _) ->
          "strong elimination on non-small inductive types leads to paradoxes."
      | _ -> "wrong arity"

exception Arity of (constr * constr * string) option

let is_correct_arity env sigma kelim (c,p) indf (pt,t) = 
  let rec srec (pt,t) =
    let pt' = whd_betadeltaiota env sigma pt in
    let t' = whd_betadeltaiota env sigma t in
    match kind_of_term pt', kind_of_term t' with
      | IsProd (_,a1,a2), IsProd (_,a1',a2') ->
          if is_conv env sigma a1 a1' then
            srec (a2,a2') 
          else 
	    raise (Arity None)
      | IsProd (_,a1,a2), _ -> 
          let k = whd_betadeltaiota env sigma a2 in 
          let ksort = (match k with DOP0(Sort s) -> s 
			 | _ -> raise (Arity None)) in
	  let ind = build_dependent_inductive indf in
          if is_conv env sigma a1 ind then
            if List.exists (base_sort_cmp CONV ksort) kelim then
	      (true,k)
            else 
	      raise (Arity (Some(k,t',error_elim_expln env sigma k t')))
	  else 
	    raise (Arity None)
      | k, IsProd (_,_,_) ->
	  raise (Arity None)
      | k, ki -> 
	  let ksort = (match k with IsSort s -> s 
                         | _ ->  raise (Arity None)) in
          if List.exists (base_sort_cmp CONV ksort) kelim then 
	    false, pt'
          else 
	    raise (Arity (Some(pt',t',error_elim_expln env sigma pt' t')))
in 
  try srec (pt,t)
  with Arity kinds ->
    let listarity =
      (List.map (make_arity env true indf) kelim)
      @(List.map (make_arity env false indf) kelim)
    in 
    let ind = mis_inductive (fst (dest_ind_family indf)) in
    error_elim_arity CCI env ind listarity c p pt kinds


let find_case_dep_nparams env sigma (c,p) (IndFamily (mis,_) as indf) typP =
  let kelim = mis_kelim mis in
  let arsign,s = get_arity indf in
  let glob_t = prod_it (mkSort s) arsign in
  let (dep,_) = is_correct_arity env sigma kelim (c,p) indf (typP,glob_t) in
  dep

(* type_case_branches type un <p>Case c of ... end 
   ct = type de c, si inductif il a la forme APP(mI,largs), sinon raise Induc
   pt = sorte de p
   type_case_branches retourne (lb, lr); lb est le vecteur des types
   attendus dans les branches du Case; lr est le type attendu du resultat
 *)

let type_case_branches env sigma (IndType (indf,realargs)) pt p c =
  let dep = find_case_dep_nparams env sigma (c,p) indf pt in
  let constructs = get_constructors indf in
  let lc = Array.map (build_branch_type env dep p) constructs in
  if dep then
    (lc, beta_applist (p,(realargs@[c])))
  else 
    (lc, beta_applist (p,realargs))

let check_branches_message env sigma (c,ct) (explft,lft) = 
  let expn = Array.length explft and n = Array.length lft in
  if n<>expn then error_number_branches CCI env c ct expn;
  for i = 0 to n-1 do
    if not (is_conv_leq env sigma lft.(i) (explft.(i))) then
      error_ill_formed_branch CCI env c i (nf_betaiota env sigma lft.(i))
	(nf_betaiota env sigma explft.(i))
  done

let type_of_case env sigma ci pj cj lfj =
  let lft = Array.map (fun j -> body_of_type j.uj_type) lfj in
  let indspec =
    try find_rectype env sigma (body_of_type cj.uj_type)
    with Induc ->
      error_case_not_inductive CCI env cj.uj_val (body_of_type cj.uj_type) in
  let (bty,rslty) =
    type_case_branches env sigma indspec (body_of_type pj.uj_type) pj.uj_val cj.uj_val in
  let kind = mysort_of_arity env sigma (body_of_type pj.uj_type) in
  check_branches_message env sigma (cj.uj_val,body_of_type cj.uj_type) (bty,lft);
  { uj_val  = mkMutCase (ci, pj.uj_val, cj.uj_val, Array.map j_val_only lfj);
    uj_type = make_typed rslty kind }

(* Prop and Set *)

let judge_of_prop =
  { uj_val = DOP0(Sort prop);
    uj_type = make_typed (DOP0(Sort type_0)) type_1 }

let judge_of_set =
  { uj_val = DOP0(Sort spec);
    uj_type = make_typed (DOP0(Sort type_0)) type_1 }

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

(* Type of Type(i). *)

let judge_of_type u =
  let (uu,uuu,c) = super_super u in
  { uj_val = DOP0 (Sort (Type u));
    uj_type = make_typed (DOP0(Sort (Type uu))) (Type uuu) },
  c

let type_of_sort c =
  match c with
    | DOP0 (Sort (Type u)) -> let (uu,cst) = super u in Type uu, cst
    | DOP0 (Sort (Prop _)) -> Type prop_univ, Constraint.empty
    | _ -> invalid_arg "type_of_sort"

(* Type of a lambda-abstraction. *)

let sort_of_product domsort rangsort g =
  match rangsort with
    (* Product rule (s,Prop,Prop) *) 
    | Prop _ -> rangsort, Constraint.empty
    | Type u2 ->
        (match domsort with
           (* Product rule (Prop,Type_i,Type_i) *)
           | Prop _ -> rangsort, Constraint.empty
           (* Product rule (Type_i,Type_i,Type_i) *) 
           | Type u1 -> let (u12,cst) = sup u1 u2 g in Type u12, cst)

let sort_of_product_without_univ domsort rangsort =
  match rangsort with
    | Prop _ -> rangsort
    | Type u2 ->
        (match domsort with
           | Prop _ -> rangsort
           | Type u1 -> Type dummy_univ)

let generalize_without_universes (_,_,var as d) c =
  typed_combine
    (fun _ c -> mkNamedProd_or_LetIn d c)
    sort_of_product_without_univ
    var c

let typed_product env name var c =
  (* Gros hack ! *)
  let rcst = ref Constraint.empty in
  let hacked_sort_of_product s1 s2 =
    let (s,cst) = sort_of_product s1 s2 (universes env) in (rcst:=cst; s) in
  typed_combine (fun c t -> mkProd (name,c,t)) hacked_sort_of_product var c,
  !rcst

let abs_rel env sigma name var j =
  let cvar = incast_type var in
  let typ,cst = typed_product env name var j.uj_type in
  { uj_val = mkLambda (name, cvar, j.uj_val);
    uj_type = typ },
  cst

(* Type of a product. *)

let gen_rel env sigma name varj j =
  let var = assumption_of_type_judgment varj in
  match whd_betadeltaiota env sigma (body_of_type j.uj_type) with
    | DOP0(Sort s) ->
	let (s',g) = sort_of_product varj.utj_type s (universes env) in
	let res_type = mkSort s' in
	let (res_kind,g') = type_of_sort res_type in
        { uj_val = mkProd (name, incast_type var, j.uj_val);
          uj_type = make_typed res_type res_kind },
	g'
    | _ -> 
(* 	if is_small (level_of_type j.uj_type) then (* message historique ?? *)
	  error "Proof objects can only be abstracted" 
	else
*)
	  error_generalization CCI env sigma (name,var) j

(* Type of a cast. *)
	    
let cast_rel env sigma cj tj =
  let tj = assumption_of_judgment env sigma tj in
  if is_conv_leq env sigma (body_of_type cj.uj_type) (body_of_type tj) then
    { uj_val = j_val_only cj;
      uj_type = tj }
  else 
    error_actual_type CCI env cj.uj_val (body_of_type cj.uj_type) (body_of_type tj)

(* Type of an application. *)

let apply_rel_list env sigma nocheck argjl funj =
  let rec apply_rec n typ cst = function
    | [] -> 
	{ uj_val  = applist (j_val_only funj, List.map j_val_only argjl);
          uj_type = typed_app (fun _ -> typ) funj.uj_type },
	cst
    | hj::restjl ->
        match kind_of_term (whd_betadeltaiota env sigma typ) with
          | IsProd (_,c1,c2) ->
              if nocheck then
                apply_rec (n+1) (subst1 hj.uj_val c2) cst restjl
	      else 
		(try 
		   let c = conv_leq env sigma (body_of_type hj.uj_type) c1 in
		   let cst' = Constraint.union cst c in
		   apply_rec (n+1) (subst1 hj.uj_val c2) cst' restjl
		 with NotConvertible -> 
		   error_cant_apply_bad_type CCI env sigma
		     (n,body_of_type hj.uj_type,c1)
		     funj argjl)
          | _ ->
	      error_cant_apply_not_functional CCI env funj argjl
  in 
  apply_rec 1 (body_of_type funj.uj_type) Constraint.empty argjl


(* Fixpoints. *)

(* Check if t is a subterm of Rel n, and gives its specification, 
   assuming lst already gives index of
   subterms with corresponding specifications of recursive arguments *)

(* A powerful notion of subterm *)

let find_sorted_assoc p = 
  let rec findrec = function 
    | (a,ta)::l -> 
	if a < p then findrec l else if a = p then ta else raise Not_found
    | _ -> raise Not_found
  in 
  findrec

let map_lift_fst_n m = List.map (function (n,t)->(n+m,t))
let map_lift_fst = map_lift_fst_n 1

let rec instantiate_recarg sp lrc ra = 
  match ra with 
    | Mrec(j)        -> Imbr((sp,j),lrc)
    | Imbr(ind_sp,l) -> Imbr(ind_sp, List.map (instantiate_recarg sp lrc) l)
    | Norec          -> Norec
    | Param(k)       -> List.nth lrc k

(* propagate checking for F,incorporating recursive arguments *)
let check_term env mind_recvec f = 
  let rec crec n l (lrec,c) = 
    match lrec, kind_of_term (strip_outer_cast c) with
      | (Param(_)::lr, IsLambda (_,_,b)) -> 
          let l' = map_lift_fst l in
          crec (n+1) l' (lr,b)
      | (Norec::lr, IsLambda (_,_,b)) -> 
          let l' = map_lift_fst l in
          crec (n+1) l' (lr,b)
      | (Mrec(i)::lr, IsLambda (_,_,b)) -> 
          let l' = map_lift_fst l in
          crec (n+1) ((1,mind_recvec.(i))::l') (lr,b)
      | (Imbr((sp,i) as ind_sp,lrc)::lr, IsLambda (_,_,b)) -> 
          let l' = map_lift_fst l in
          let sprecargs = 
	    mis_recargs (lookup_mind_specif (ind_sp,[||]) env) in
          let lc = 
	    Array.map (List.map (instantiate_recarg sp lrc)) sprecargs.(i)
	  in
          crec (n+1) ((1,lc)::l') (lr,b)
      | _,_ -> f n l (strip_outer_cast c)
  in 
  crec

let is_inst_var env sigma k c = 
  match whd_betadeltaiota_stack env sigma c [] with 
    | (Rel n,_) -> n=k
    | _ -> false

let is_subterm_specif env sigma lcx mind_recvec = 
  let rec crec n lst c = 
    let f,l = whd_betadeltaiota_stack env sigma c [] in
    match kind_of_term f with 
      | IsRel k -> find_sorted_assoc k lst

      | IsMutCase ( _,_,c,br) ->
          if Array.length br = 0 then
            [||] 
          else
            let lcv = 
	      (try 
		 if is_inst_var env sigma n c then lcx else (crec n lst c) 
               with Not_found -> (Array.create (Array.length br) []))
            in 
	    assert (Array.length br = Array.length lcv);
            let stl = 
	      array_map2
                (fun lc a -> 
                   check_term env mind_recvec crec n lst (lc,a)) lcv br 
            in 
	    stl.(0)
	       
      | IsFix ((recindxs,i),(typarray,funnames,bodies)) ->
          let nbfix   = List.length funnames in
          let decrArg = recindxs.(i) in 
          let theBody = bodies.(i)   in
          let (_,strippedBody) = decompose_lam_n (decrArg+1) theBody in
          let nbOfAbst = nbfix+decrArg+1 in
          let newlst = 
            if List.length l < (decrArg+1) then
              ((nbOfAbst,lcx) :: (map_lift_fst_n nbOfAbst lst))
            else 
              let theDecrArg  = List.nth l decrArg in
              let recArgsDecrArg = 
                try (crec n lst theDecrArg)
	        with Not_found -> Array.create 0 [] 
              in 
	      if (Array.length recArgsDecrArg)=0 then
		(nbOfAbst,lcx) :: (map_lift_fst_n nbOfAbst lst)
              else 
		(1,recArgsDecrArg) ::
                (nbOfAbst,lcx) ::
                (map_lift_fst_n nbOfAbst lst)
          in 
	  crec (n+nbOfAbst) newlst strippedBody
	    
      | IsLambda (_,_,b) when l=[] -> 
          let lst' = map_lift_fst lst in
          crec (n+1) lst' b

      (*** Experimental change *************************)
      | IsMeta _ -> [||]
      | _ -> raise Not_found
  in 
  crec

let is_subterm env sigma lcx mind_recvec n lst c = 
  try 
    let _ = is_subterm_specif env sigma lcx mind_recvec n lst c in true 
  with Not_found -> 
    false

exception FixGuardError of guard_error

(* Auxiliary function: it checks a condition f depending on a deBrujin
   index for a certain number of abstractions *)

let rec check_subterm_rec_meta env sigma vectn k def =
  (* If k<0, it is a general fixpoint *)
  (k < 0) or
  (let nfi = Array.length vectn in 
   (* check fi does not appear in the k+1 first abstractions, 
      gives the type of the k+1-eme abstraction  *)
   let rec check_occur n def = 
     match kind_of_term (strip_outer_cast def) with
       | IsLambda (_,a,b) -> 
	   if noccur_with_meta n nfi a then
             if n = k+1 then (a,b) else check_occur (n+1) b
           else 
	     anomaly "check_subterm_rec_meta: Bad occurrence of recursive call"
       | _ -> raise (FixGuardError NotEnoughAbstractionInFixBody) in
   let (c,d) = check_occur 1 def in 
   let ((sp,tyi),_ as mind, largs) = 
     try find_minductype env sigma c 
     with Induc -> raise (FixGuardError RecursionNotOnInductiveType) in
   let mind_recvec = mis_recargs (lookup_mind_specif mind env) in 
   let lcx = mind_recvec.(tyi)  in
   (* n   = decreasing argument in the definition;
      lst = a mapping var |-> recargs
      t   = the term to be checked
   *)
   let rec check_rec_call n lst t = 
     (* n gives the index of the recursive variable *)
     (noccur_with_meta (n+k+1) nfi t) or 
     (* no recursive call in the term *)
     (let f,l = whd_betadeltaiota_stack env sigma t [] in
      match kind_of_term f with
	| IsRel p -> 
	    if n+k+1 <= p & p < n+k+nfi+1 then
	      (* recursive call *) 
	      let glob = nfi+n+k-p in  (* the index of the recursive call *) 
	      let np = vectn.(glob) in (* the decreasing arg of the rec call *)
	      if List.length l > np then 
		(match list_chop np l with
		     (la,(z::lrest)) -> 
	               if (is_subterm env sigma lcx mind_recvec n lst z) 
                       then List.for_all (check_rec_call n lst) (la@lrest)
                       else raise (FixGuardError RecursionOnIllegalTerm)
		   | _ -> assert false)
	      else raise (FixGuardError NotEnoughArgumentsForFixCall)
	    else List.for_all (check_rec_call n lst) l        

	| IsMutCase (ci,p,c_0,lrest) ->
            let lc = 
	      (try 
		 if is_inst_var env sigma n c_0 then 
		   lcx 
		 else 
		   is_subterm_specif env sigma lcx mind_recvec n lst c_0
	       with Not_found -> 
		 Array.create (Array.length lrest) []) 
	    in
            (array_for_all2
	       (fun c_0 a -> 
		  check_term env mind_recvec (check_rec_call) n lst (c_0,a))
	       lc lrest) 
	    && (List.for_all (check_rec_call n lst) (c_0::p::l)) 

  (* Enables to traverse Fixpoint definitions in a more intelligent
     way, ie, the rule :

     if - g = Fix g/1 := [y1:T1]...[yp:Tp]e &
        - f is guarded with respect to the set of pattern variables S 
          in a1 ... am        &
        - f is guarded with respect to the set of pattern variables S 
          in T1 ... Tp        &
        - ap is a sub-term of the formal argument of f &
        - f is guarded with respect to the set of pattern variables S+{yp}
          in e
     then f is guarded with respect to S in (g a1 ... am).

     Eduardo 7/9/98 *)

	| IsFix ((recindxs,i),(typarray,funnames,bodies)) ->
            (List.for_all (check_rec_call n lst) l) &&
            let nbfix = List.length funnames in
            let decrArg = recindxs.(i) in
            if (List.length l < (decrArg+1)) then
              (array_for_all (check_rec_call n lst) typarray)
	      &&
	      (array_for_all
		 (check_rec_call (n+nbfix) (map_lift_fst_n nbfix lst))
		 bodies)
            else 
              let theDecrArg  = List.nth l decrArg in
              let recArgsDecrArg = 
                try 
		  is_subterm_specif env sigma lcx mind_recvec n lst theDecrArg
	        with Not_found -> 
		  Array.create 0 [] 
              in 
	      if (Array.length recArgsDecrArg)=0 then
		(array_for_all (check_rec_call n lst) typarray)
		&&
		(array_for_all
		   (check_rec_call (n+nbfix) (map_lift_fst_n nbfix lst))
		   bodies)
              else 
                let theBody = bodies.(i)   in
                let (gamma,strippedBody) = 
		  decompose_lam_n (decrArg+1) theBody in
                let absTypes = List.map snd gamma in 
                let nbOfAbst = nbfix+decrArg+1 in
                let newlst = 
		  ((1,recArgsDecrArg)::(map_lift_fst_n nbOfAbst lst))
                in 
		((array_for_all
		    (fun t -> check_rec_call n lst t)
		    typarray) &&
                 (list_for_all_i (fun n -> check_rec_call n lst) n absTypes) &
                 (check_rec_call (n+nbOfAbst) newlst strippedBody))

	| IsCast (a,b) -> 
	    (check_rec_call n lst a) &&
            (check_rec_call n lst b) &&
            (List.for_all (check_rec_call n lst) l)

	| IsLambda (_,a,b) -> 
	    (check_rec_call n lst a) &&
            (check_rec_call (n+1) (map_lift_fst lst) b) &&
            (List.for_all (check_rec_call n lst) l)

	| IsProd (_,a,b) -> 
	    (check_rec_call n lst a) &&
            (check_rec_call (n+1) (map_lift_fst lst) b) &&
            (List.for_all (check_rec_call n lst) l)

	| IsLetIn (_,a,b,c) -> 
	    (check_rec_call n lst a) &&
	    (check_rec_call n lst b) &&
            (check_rec_call (n+1) (map_lift_fst lst) c) &&
            (List.for_all (check_rec_call n lst) l)

	| IsMutInd (_,la) -> 
	     (array_for_all (check_rec_call n lst) la) &&
             (List.for_all (check_rec_call n lst) l)

	| IsMutConstruct (_,la) -> 
	     (array_for_all (check_rec_call n lst) la) &&
             (List.for_all (check_rec_call n lst) l)

	| IsConst (_,la) -> 
	    (array_for_all (check_rec_call n lst) la) &&
            (List.for_all (check_rec_call n lst) l)

	| IsAppL (f,la) -> 
	    (check_rec_call n lst f) &&
	    (List.for_all (check_rec_call n lst) la) &&
            (List.for_all (check_rec_call n lst) l)

	| IsCoFix (i,(typarray,funnames,bodies)) ->
	    let nbfix = Array.length bodies in
	    (array_for_all (check_rec_call n lst) typarray) &&
            (List.for_all (check_rec_call n lst) l) &&
	    (array_for_all
	       (check_rec_call (n+nbfix) (map_lift_fst_n nbfix lst))
	       bodies)

	| IsEvar (_,la) -> 
	    (array_for_all (check_rec_call n lst) la) &&
            (List.for_all (check_rec_call n lst) l)

	| IsMeta _ -> true

	| IsVar _ | IsSort _ ->  List.for_all (check_rec_call n lst) l

	| IsXtra _ ->  List.for_all (check_rec_call n lst) l
     )
     
   in 
   check_rec_call 1 [] d)

(* vargs is supposed to be built from A1;..Ak;[f1]..[fk][|d1;..;dk|]
and vdeft is [|t1;..;tk|] such that f1:A1,..,fk:Ak |- di:ti
nvect is [|n1;..;nk|] which gives for each recursive definition 
the inductive-decreasing index 
the function checks the convertibility of ti with Ai *)

let check_fix env sigma ((nvect,bodynum),(types,names,bodies)) =
  let nbfix = Array.length bodies in 
  if nbfix = 0
    or Array.length nvect <> nbfix 
    or Array.length types <> nbfix
    or List.length names <> nbfix
    or bodynum < 0
    or bodynum >= nbfix
  then anomaly "Ill-formed fix term";
  for i = 0 to nbfix - 1 do
    try
      let _ = check_subterm_rec_meta env sigma nvect nvect.(i) bodies.(i) in ()
    with FixGuardError err ->
      error_ill_formed_rec_body	CCI env err (List.rev names) i bodies
  done 

(* Co-fixpoints. *)

exception CoFixGuardError of guard_error

let check_guard_rec_meta env sigma nbfix def deftype = 
  let rec codomain_is_coind c  =
    let b = whd_betadeltaiota env sigma (strip_outer_cast c) in
    match kind_of_term b with
      | IsProd (_,a,b) -> codomain_is_coind b 
      | _ -> 
	  try
	    find_mcoinductype env sigma b
          with Induc ->
	    raise (CoFixGuardError (CodomainNotInductiveType b))
  in
  let (mind, _) = codomain_is_coind deftype in
  let ((sp,tyi),_) = mind in
  let lvlra = (mis_recargs (lookup_mind_specif mind env)) in
  let vlra = lvlra.(tyi) in  
  let rec check_rec_call alreadygrd n vlra  t = 
    if noccur_with_meta n nbfix t then
      true 
    else 
      match whd_betadeltaiota_stack env sigma t [] with 
	| (DOP0 (Meta _), l) -> true
	      
	|  (Rel p,l) -> 
             if n <= p && p < n+nbfix then
	       (* recursive call *)
               if alreadygrd then
		 if List.for_all (noccur_with_meta n nbfix) l then
		   true
		 else 
		   raise (CoFixGuardError NestedRecursiveOccurrences)
               else 
		 raise (CoFixGuardError (UnguardedRecursiveCall t))
             else  
	       error "check_guard_rec_meta: ???"  (* ??? *)
		 
	| (DOPN (MutConstruct(_,i as cstr_sp),l), args)  ->
            let lra =vlra.(i-1) in 
            let mI = inductive_of_constructor (cstr_sp,l) in
	    let mis = lookup_mind_specif mI env in
            let _,realargs = list_chop (mis_nparams mis) args in
            let rec process_args_of_constr l lra =
              match l with
                | [] -> true 
                | t::lr ->
		    (match lra  with 
                       | [] -> 
			   anomalylabstrm "check_guard_rec_meta"
			     [< 'sTR "a constructor with an empty list";
				'sTR "of recargs is being applied" >]
                       |  (Mrec i)::lrar -> 
                            let newvlra = lvlra.(i) in
                            (check_rec_call true n newvlra t) &&
                            (process_args_of_constr lr lrar)
			    
                       |  (Imbr((sp,i) as ind_sp,lrc)::lrar)  ->
			    let mis =
			      lookup_mind_specif (ind_sp,[||]) env in
                            let sprecargs = mis_recargs mis in
                            let lc = (Array.map 
                                        (List.map 
                                           (instantiate_recarg sp lrc))
                                        sprecargs.(i))
                            in (check_rec_call true n lc t) &
                               (process_args_of_constr lr lrar)
				 
                       |  _::lrar  -> 
                            if (noccur_with_meta n nbfix t) 
                            then (process_args_of_constr lr lrar)
                            else raise (CoFixGuardError
					  (RecCallInNonRecArgOfConstructor t)))
            in (process_args_of_constr realargs lra)
		 
		 
	| (DOP2(Lambda,a,DLAM(_,b)),[]) -> 
            if (noccur_with_meta n nbfix a) then
              check_rec_call alreadygrd (n+1)  vlra b
            else 
	      raise (CoFixGuardError (RecCallInTypeOfAbstraction t))
	      
	| (DOPN(CoFix(j),vargs) as cofix,l) ->
            if (List.for_all (noccur_with_meta n nbfix) l)
            then 
	      let (j,(varit,lna,vdefs)) = destFix cofix in
              let nbfix = Array.length vdefs in
	      if (array_for_all (noccur_with_meta n nbfix) varit) then
		(array_for_all (check_rec_call alreadygrd (n+1) vlra) vdefs)
		&&
		(List.for_all (check_rec_call alreadygrd (n+1) vlra) l) 
              else 
		raise (CoFixGuardError (RecCallInTypeOfDef cofix))
	    else
	      raise (CoFixGuardError (UnguardedRecursiveCall cofix))

	| (DOPN(MutCase _,_) as mc,l) -> 
            let (_,p,c,vrest) = destCase mc in
            if (noccur_with_meta n nbfix p) then
              if (noccur_with_meta n nbfix c) then
		if (List.for_all (noccur_with_meta n nbfix) l) then
		  (array_for_all (check_rec_call alreadygrd n vlra) vrest)
		else 
		  raise (CoFixGuardError (RecCallInCaseFun mc))
              else 
		raise (CoFixGuardError (RecCallInCaseArg mc))
            else 
	      raise (CoFixGuardError (RecCallInCasePred mc))
              
	| _    -> raise (CoFixGuardError NotGuardedForm)
	      
  in 
  check_rec_call false 1 vlra def

(* The  function which checks that the whole block of definitions 
   satisfies the guarded condition *)

let check_cofix env sigma (bodynum,(types,names,bodies)) = 
  let nbfix = Array.length bodies in 
  for i = 0 to nbfix-1 do
    try 
      let _ = check_guard_rec_meta env sigma nbfix bodies.(i) types.(i) in ()
    with CoFixGuardError err -> 
      error_ill_formed_rec_body CCI env err (List.rev names) i bodies
  done
(*
let check_cofix env sigma f = 
  match f with
    | DOPN(CoFix(j),vargs) -> 
	let nbfix = let nv = Array.length vargs in 
        if nv < 2 then
          error "Ill-formed recursive definition" 
        else 
	  nv-1 
	in
	let varit = Array.sub vargs 0 nbfix in
	let ldef  = array_last vargs in
	let la    = Array.length varit in
	let (lna,vdefs) = decomp_DLAMV_name la ldef in
	let vlna = Array.of_list lna in
	let check_type i = 
	  try 
	    let _ = 
	      check_guard_rec_meta env sigma nbfix vdefs.(i) varit.(i) in 
	    ()
	  with UserError (s,str) -> 
	    error_ill_formed_rec_body CCI env str lna i vdefs 
	in
	for i = 0 to nbfix-1 do check_type i done
    | _ -> assert false
*)

(* Checks the type of a (co)fixpoint.
   Fix and CoFix are typed the same way; only the guard condition differs. *)

exception IllBranch of int

let type_fixpoint env sigma lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Array.length lar = lt);
  try
    conv_forall2_i
      (fun i env sigma def ar -> 
	 try conv_leq env sigma def (lift lt ar) 
	 with NotConvertible -> raise (IllBranch i))
      env sigma
      (Array.map (fun j -> body_of_type j.uj_type) vdefj) (Array.map body_of_type lar)
  with IllBranch i ->
    error_ill_typed_rec_body CCI env i lna vdefj lar


(* A function which checks that a term well typed verifies both
   syntaxic conditions *)

let control_only_guard env sigma = 
  let rec control_rec c = match kind_of_term c with
    | IsRel _ | IsVar _    -> ()
    | IsSort _ | IsMeta _ | IsXtra _ -> ()
    | IsCoFix (_,(tys,_,bds) as cofix) ->
	check_cofix env sigma cofix;
	Array.iter control_rec tys;
	Array.iter control_rec bds;
    | IsFix (_,(tys,_,bds) as fix) ->
	check_fix env sigma fix; 
	Array.iter control_rec tys;
	Array.iter control_rec bds;
    | IsMutCase(_,p,c,b) ->control_rec p;control_rec c;Array.iter control_rec b
    | IsMutInd (_,cl)       -> Array.iter control_rec cl
    | IsMutConstruct (_,cl) -> Array.iter control_rec cl
    | IsConst (_,cl)        -> Array.iter control_rec cl
    | IsEvar (_,cl)         -> Array.iter control_rec cl
    | IsAppL (_,cl)         -> List.iter control_rec cl
    | IsCast (c1,c2)       -> control_rec c1; control_rec c2
    | IsProd (_,c1,c2)     -> control_rec c1; control_rec c2
    | IsLambda (_,c1,c2)   -> control_rec c1; control_rec c2
    | IsLetIn (_,c1,c2,c3) -> control_rec c1; control_rec c2; control_rec c3
  in 
  control_rec 

    
