(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Univ
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

let j_val j = j.uj_val

(* This should be a type intended to be assumed *)
let assumption_of_judgment env sigma j =
  match kind_of_term(whd_betadeltaiota env sigma (body_of_type j.uj_type)) with
    | IsSort s -> j.uj_val
    | _ -> error_assumption CCI env j.uj_val

(*
let aojkey = Profile.declare_profile "assumption_of_judgment";;
let assumption_of_judgment env sigma j
  = Profile.profile3 aojkey assumption_of_judgment env sigma j;;
*)

(* This should be a type (a priori without intension to be an assumption) *)
let type_judgment env sigma j =
  match kind_of_term(whd_betadeltaiota env sigma (body_of_type j.uj_type)) with
    | IsSort s -> {utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_type CCI env j


(************************************************)
(* Incremental typing rules: builds a typing judgement given the *)
(* judgements for the subterms. *)

(* Type of sorts *)

(* Prop and Set *)

let judge_of_prop =
  { uj_val = mkSort prop;
    uj_type = mkSort type_0 }

let judge_of_set =
  { uj_val = mkSort spec;
    uj_type = mkSort type_0 }

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

(* Type of Type(i). *)

let judge_of_type u =
  let (uu,c) = super u in
  { uj_val = mkSort (Type u);
    uj_type = mkSort (Type uu) },
  c

(*
let type_of_sort c =
  match kind_of_term c with
    | IsSort (Type u) -> let (uu,cst) = super u in Type uu, cst
    | IsSort (Prop _) -> Type prop_univ, Constraint.empty
    | _ -> invalid_arg "type_of_sort"
*)

(* Type of a de Bruijn index. *)
	  
let relative env n = 
  try
    let (_,typ) = lookup_rel_type n env in
    { uj_val  = mkRel n;
      uj_type = type_app (lift n) typ }
  with Not_found -> 
    error_unbound_rel CCI env n

(*
let relativekey = Profile.declare_profile "relative";;
let relative env sigma n = Profile.profile3 relativekey relative env sigma n;;
*)

(* Management of context of variables. *)

(* Checks if a context of variable is included in another one. *)
(*
let rec hyps_inclusion env sigma sign1 sign2 =
  if sign1 = empty_named_context then true
  else
    let (id1,ty1) = hd_sign sign1 in
    let rec search sign2 =
      if sign2 = empty_named_context then false
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
  let hyps' = named_context env in
  if not (hyps_inclusion env sigma hyps hyps') then
    error_reference_variables CCI env id
*)
(* Instantiation of terms on real arguments. *)

let type_of_constant = Instantiate.constant_type

(*
let tockey = Profile.declare_profile "type_of_constant";;
let type_of_constant env sigma c 
  = Profile.profile3 tockey type_of_constant env sigma c;;
*)

(* Type of an existential variable. Not used in kernel. *)
let type_of_existential env sigma ev =
  Instantiate.existential_type sigma ev


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

(* [abs_rel env sigma name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let abs_rel env sigma name var j =
  { uj_val = mkLambda (name, var, j.uj_val);
    uj_type = mkProd (name, var, j.uj_type) },
  Constraint.empty

let judge_of_letin env sigma name defj j =
  let v = match kind_of_term defj.uj_val with
      IsCast(c,t) -> c
    | _ -> defj.uj_val in
  ({ uj_val = mkLetIn (name, v, defj.uj_type, j.uj_val) ;
    uj_type = type_app (subst1 v) j.uj_type },
  Constraint.empty)

(* [gen_rel env sigma name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)

(* Type of an application. *)

let apply_rel_list env sigma nocheck argjl funj =
  let rec apply_rec n typ cst = function
    | [] -> 
	{ uj_val  = applist (j_val funj, List.map j_val argjl);
          uj_type = type_app (fun _ -> typ) funj.uj_type },
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
		   error_cant_apply_bad_type CCI env
		     (n,c1,body_of_type hj.uj_type)
		     funj argjl)

          | _ ->
	      error_cant_apply_not_functional CCI env funj argjl
  in 
  apply_rec 1 (body_of_type funj.uj_type) Constraint.empty argjl

(*
let applykey = Profile.declare_profile "apply_rel_list";;
let apply_rel_list env sigma nocheck argjl funj
  = Profile.profile5 applykey apply_rel_list env sigma nocheck argjl funj;;
*)

(* Type of product *)
let gen_rel env sigma name t1 t2 =
  let (s,g) = sort_of_product t1.utj_type t2.utj_type (universes env) in
  { uj_val = mkProd (name, t1.utj_val, t2.utj_val);
    uj_type = mkSort s },
  g

(* [cast_rel env sigma (typ1,s1) j] implements the rule

    env, sigma |- cj.uj_val:cj.uj_type    cst, env, sigma |- cj.uj_type = t
    ---------------------------------------------------------------------
         cst, env, sigma |- cj.uj_val:t
*)

(* Type of casts *)    
let cast_rel env sigma cj t =
  try 
    let cst = conv_leq env sigma (body_of_type cj.uj_type) t in
    { uj_val = j_val cj;
      uj_type = t },
    cst
  with NotConvertible ->
    error_actual_type CCI env cj.uj_val (body_of_type cj.uj_type) t

(* Inductive types. *)

let type_of_inductive env sigma i =
  (* TODO: check args *)
  mis_arity (lookup_mind_specif i env)

(*
let toikey = Profile.declare_profile "type_of_inductive";;
let type_of_inductive env sigma i
  = Profile.profile3 toikey type_of_inductive env sigma i;;
*)

(* Constructors. *)

let type_of_constructor env sigma cstr =
  mis_constructor_type
    (index_of_constructor cstr) 
    (lookup_mind_specif (inductive_of_constructor cstr) env)

(*
let tockey = Profile.declare_profile "type_of_constructor";;
let type_of_constructor env sigma cstr
  = Profile.profile3 tockey type_of_constructor env sigma cstr;;
*)

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

let is_correct_arity env sigma kelim (c,pj) indf t = 
  let rec srec (pt,t) u =
    let pt' = whd_betadeltaiota env sigma pt in
    let t' = whd_betadeltaiota env sigma t in
    match kind_of_term pt', kind_of_term t' with
      | IsProd (_,a1,a2), IsProd (_,a1',a2') ->
          let univ =
            try conv env sigma a1 a1'
            with NotConvertible -> raise (Arity None) in
          srec (a2,a2') (Constraint.union u univ)
      | IsProd (_,a1,a2), _ -> 
          let k = whd_betadeltaiota env sigma a2 in 
          let ksort = (match kind_of_term k with IsSort s -> s 
			 | _ -> raise (Arity None)) in
	  let ind = build_dependent_inductive indf in
          let univ =
            try conv env sigma a1 ind
            with NotConvertible -> raise (Arity None) in
          if List.exists (base_sort_cmp CONV ksort) kelim then
	    ((true,k), Constraint.union u univ)
          else 
	    raise (Arity (Some(k,t',error_elim_expln env sigma k t')))
      | k, IsProd (_,_,_) ->
	  raise (Arity None)
      | k, ki -> 
	  let ksort = (match k with IsSort s -> s 
                         | _ ->  raise (Arity None)) in
          if List.exists (base_sort_cmp CONV ksort) kelim then 
	    (false, pt'), u
          else 
	    raise (Arity (Some(pt',t',error_elim_expln env sigma pt' t')))
  in 
  try srec (pj.uj_type,t) Constraint.empty
  with Arity kinds ->
    let listarity =
      (List.map (make_arity env true indf) kelim)
      @(List.map (make_arity env false indf) kelim)
    in 
    let ind = mis_inductive (fst (dest_ind_family indf)) in
    error_elim_arity CCI env ind listarity c pj kinds


let find_case_dep_nparams env sigma (c,pj) (IndFamily (mis,_) as indf) =
  let kelim = mis_kelim mis in
  let arsign,s = get_arity indf in
  let glob_t = it_mkProd_or_LetIn (mkSort s) arsign in
  let ((dep,_),univ) =
    is_correct_arity env sigma kelim (c,pj) indf glob_t in
  (dep,univ)

(* type_case_branches type un <p>Case c of ... end 
   IndType (indf,realargs) = type de c
   pt = sorte de p
   type_case_branches retourne (lb, lr); lb est le vecteur des types
   attendus dans les branches du Case; lr est le type attendu du resultat
 *)

let type_case_branches env sigma (IndType (indf,realargs)) pj c =
  let p = pj.uj_val in
  let (dep,univ) = find_case_dep_nparams env sigma (c,pj) indf in
  let constructs = get_constructors indf in
  let lc = Array.map (build_branch_type env dep p) constructs in
  if dep then
    (lc, beta_applist (p,(realargs@[c])), univ)
  else 
    (lc, beta_applist (p,realargs), univ)

let check_branches_message env sigma cj (explft,lft) = 
  let expn = Array.length explft and n = Array.length lft in
  if n<>expn then error_number_branches CCI env cj expn;
  let univ = ref Constraint.empty in
  (for i = 0 to n-1 do
    try
      univ := Constraint.union !univ
        (conv_leq env sigma lft.(i) (explft.(i)))
    with NotConvertible ->
      error_ill_formed_branch CCI env cj.uj_val i lft.(i) explft.(i)
  done;
  !univ)

let nparams_of (IndType (IndFamily (mis,_),_)) = mis_nparams mis 

let judge_of_case env sigma (np,_ as ci) pj cj lfj =
  let lft = Array.map (fun j -> body_of_type j.uj_type) lfj in
  let indspec =
    try find_rectype env sigma (body_of_type cj.uj_type)
    with Induc -> error_case_not_inductive CCI env cj in
  if np <> nparams_of indspec then 
    anomaly "judge_of_case: wrong parameters number";
  let (bty,rslty,univ) = type_case_branches env sigma indspec pj cj.uj_val in
  let kind = mysort_of_arity env sigma (body_of_type pj.uj_type) in
  let univ' = check_branches_message env sigma cj (bty,lft) in
  ({ uj_val  = mkMutCase (ci, (nf_betaiota pj.uj_val), cj.uj_val, Array.map j_val lfj);
     uj_type = rslty },
  Constraint.union univ univ')

(*
let tocasekey = Profile.declare_profile "type_of_case";;
let type_of_case env sigma ci pj cj lfj
  = Profile.profile6 tocasekey type_of_case env sigma ci pj cj lfj;;
*)

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

(* To each inductive definition corresponds an array describing the
   structure of recursive arguments for each constructor, we call it
   the recursive spec of the type (it has type recargs vect).  For
   checking the guard, we start from the decreasing argument (Rel n)
   with its recursive spec.  During checking the guardness condition,
   we collect patterns variables corresponding to subterms of n, each
   of them with its recursive spec.  They are organised in a list lst
   of type (int * recargs) list which is sorted with respect to the
   first argument.
*)

(*
   f is a function of type
     env -> int -> (int * recargs) list -> constr -> 'a 

   c is a branch of an inductive definition corresponding to the spec
   lrec.  mind_recvec is the recursive spec of the inductive
   definition of the decreasing argument n.

   check_term env mind_recvec f n lst (lrec,c) will pass the lambdas
   of c corresponding to pattern variables and collect possibly new
   subterms variables and apply f to the body of the branch with the
   correct env and decreasing arg.
*)

let check_term env mind_recvec f = 
  let rec crec env n lst (lrec,c) = 
    let c' = strip_outer_cast c in 
    match lrec, kind_of_term c' with 
	(ra::lr,IsLambda (x,a,b)) ->
          let lst' = map_lift_fst lst
          and env' = push_rel_assum (x,a) env
          and n'=n+1 
          in begin match ra with 
	      Mrec(i) -> crec env' n' ((1,mind_recvec.(i))::lst') (lr,b)
            | Imbr((sp,i) as ind_sp,lrc) ->           
	        let sprecargs =
                  mis_recargs (lookup_mind_specif (ind_sp,[||]) env) in
                let lc = Array.map
                  (List.map (instantiate_recarg sp lrc)) sprecargs.(i)
                in crec env' n' ((1,lc)::lst') (lr,b)
	    | _ -> crec env' n' lst' (lr,b) end
      | (_,_) -> f env n lst c'
  in crec env

(* c is supposed to be in beta-delta-iota head normal form *)

let is_inst_var k c = 
  match kind_of_term (fst (decomp_app c)) with 
    | IsRel n -> n=k
    | _ -> false

(* 
   is_subterm_specif env sigma lcx mind_recvec n lst c 

   n is the principal arg and has recursive spec lcx, lst is the list
   of subterms of n with spec.  is_subterm_specif should test if c is
   a subterm of n and fails with Not_found if not.  In case it is, it
   should send its recursive specification.  This recursive spec
   should be the same size as the number of constructors of the type
   of c. A problem occurs when c is built by contradiction. In that
   case no spec is given.

*)
let is_subterm_specif env sigma lcx mind_recvec = 
  let rec crec env n lst c = 
    let f,l = whd_betadeltaiota_stack env sigma c in
    match kind_of_term f with 
      | IsRel k -> Some (find_sorted_assoc k lst)

      | IsMutCase ( _,_,c,br) ->
          if Array.length br = 0 then None

          else
            let def = Array.create (Array.length br) []
            in let lcv = 
	      (try 
		 if is_inst_var n c then lcx 
		 else match crec env n lst c with Some lr -> lr | None -> def
               with Not_found -> def)
            in 
	    assert (Array.length br = Array.length lcv);
            let stl = 
	      array_map2
                (fun lc a -> 
                   check_term env mind_recvec crec n lst (lc,a)) lcv br 
            in let stl0 = stl.(0) in
	    if array_for_all (fun st -> st=stl0) stl then stl0 
            else None
	       
      | IsFix ((recindxs,i),(_,typarray,bodies as recdef)) ->
          let nbfix   = Array.length typarray in
          let decrArg = recindxs.(i) in 
          let theBody = bodies.(i)   in
          let sign,strippedBody = decompose_lam_n_assum (decrArg+1) theBody in
          let nbOfAbst = nbfix+decrArg+1 in
(* when proving that the fixpoint f(x)=e is less than n, it is enough
   to prove that e is less than n assuming f is less than n
   furthermore when f is applied to a term which is strictly less than
   n, one may assume that x itself is strictly less than n
*)
          let newlst = 
            let lst' = (nbOfAbst,lcx) :: (map_lift_fst_n nbOfAbst lst) in
            if List.length l < (decrArg+1) then lst' 
            else let theDecrArg  = List.nth l decrArg in
	      try 
	      match crec env n lst theDecrArg with 
		  (Some recArgsDecrArg) -> (1,recArgsDecrArg) :: lst' 
                | None -> lst' 
	      with Not_found -> lst'
	  in let env' = push_rec_types recdef env in
	  let env'' = push_rels sign env' in
	  crec env'' (n+nbOfAbst) newlst strippedBody
	    
      | IsLambda (x,a,b) when l=[] -> 
          let lst' = map_lift_fst lst in
          crec (push_rel_assum (x, a) env) (n+1) lst' b

      (*** Experimental change *************************)
      | IsMeta _ -> None
      | _ -> raise Not_found
  in 
  crec env

let spec_subterm_strict env sigma lcx mind_recvec n lst c nb = 
    try match  is_subterm_specif env sigma lcx mind_recvec n lst c 
        with Some lr -> lr | None -> Array.create nb []
    with Not_found -> Array.create nb []

let spec_subterm_large env sigma lcx mind_recvec n lst c nb = 
  if is_inst_var n c then lcx 
  else spec_subterm_strict env sigma lcx mind_recvec n lst c nb 


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
   let rec check_occur env n def = 
     match kind_of_term (strip_outer_cast def) with
       | IsLambda (x,a,b) -> 
	   if noccur_with_meta n nfi a then
	     let env' = push_rel_assum (x, a) env in
             if n = k+1 then (env', lift 1 a, b)
	     else check_occur env' (n+1) b
           else 
	     anomaly "check_subterm_rec_meta: Bad occurrence of recursive call"
       | _ -> raise (FixGuardError NotEnoughAbstractionInFixBody) in
   let (env',c,d) = check_occur env 1 def in
   let ((sp,tyi),_ as mind, largs) = 
     try find_inductive env' sigma c 
     with Induc -> raise (FixGuardError RecursionNotOnInductiveType) in
   let mind_recvec = mis_recargs (lookup_mind_specif mind env') in 
   let lcx = mind_recvec.(tyi)  in
   (* n   = decreasing argument in the definition;
      lst = a mapping var |-> recargs
      t   = the term to be checked
   *)
   let rec check_rec_call env n lst t = 
     (* n gives the index of the recursive variable *)
     (noccur_with_meta (n+k+1) nfi t) or 
     (* no recursive call in the term *)
     (let f,l = whd_betaiotazeta_stack t in
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
                       then List.for_all (check_rec_call env n lst) (la@lrest)
                       else raise (FixGuardError RecursionOnIllegalTerm)
		   | _ -> assert false)
	      else raise (FixGuardError NotEnoughArgumentsForFixCall)
	    else List.for_all (check_rec_call env n lst) l        

	| IsMutCase (ci,p,c_0,lrest) ->
            let lc = spec_subterm_large env sigma lcx mind_recvec n lst c_0 
		       (Array.length lrest)
	    in
            (array_for_all2
	       (fun c0 a -> 
		  check_term env mind_recvec check_rec_call n lst (c0,a))
	       lc lrest) 
	    && (List.for_all (check_rec_call env n lst) (c_0::p::l)) 

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

	| IsFix ((recindxs,i),(_,typarray,bodies as recdef)) ->
            (List.for_all (check_rec_call env n lst) l) &&
            (array_for_all (check_rec_call env n lst) typarray) && 
	    let nbfix = Array.length typarray in
            let decrArg = recindxs.(i) 
            and env' = push_rec_types recdef env 
            and n' = n+nbfix
	    and lst' = map_lift_fst_n nbfix lst
	    in 
            if (List.length l < (decrArg+1)) then
	       array_for_all (check_rec_call env' n' lst') bodies
            else 
              let theDecrArg  = List.nth l decrArg in
	      (try 
		match
                  is_subterm_specif env sigma lcx mind_recvec n lst theDecrArg
		with
                    Some recArgsDecrArg -> 
		      let theBody = bodies.(i)   in
		      check_rec_call_fix_body
                        env' n' lst' (decrArg+1) recArgsDecrArg theBody
		  | None ->
                      array_for_all (check_rec_call env' n' lst') bodies
	      with Not_found ->
                array_for_all (check_rec_call env' n' lst') bodies)

	| IsCast (a,b) -> 
	    (check_rec_call env n lst a) &&
            (check_rec_call env n lst b) &&
            (List.for_all (check_rec_call env n lst) l)

	| IsLambda (x,a,b) -> 
	    (check_rec_call env n lst a) &&
            (check_rec_call (push_rel_assum (x, a) env)
	       (n+1) (map_lift_fst lst) b) &&
            (List.for_all (check_rec_call env n lst) l)

	| IsProd (x,a,b) -> 
	    (check_rec_call env n lst a) &&
            (check_rec_call (push_rel_assum (x, a) env)
	       (n+1) (map_lift_fst lst) b) &&
            (List.for_all (check_rec_call env n lst) l)

	| IsLetIn (x,a,b,c) -> 
	    anomaly "check_rec_call: should have been reduced"

	| IsMutInd (_,la) -> 
	     (array_for_all (check_rec_call env n lst) la) &&
             (List.for_all (check_rec_call env n lst) l)

	| IsMutConstruct (_,la) -> 
	     (array_for_all (check_rec_call env n lst) la) &&
             (List.for_all (check_rec_call env n lst) l)

	| IsConst (sp,la) as c -> 
            (try 
	    (array_for_all (check_rec_call env n lst) la) &&
            (List.for_all (check_rec_call env n lst) l)
	     with (FixGuardError _ ) as e
		 -> if evaluable_constant env sp then 
		   check_rec_call env n lst (whd_betadeltaiota env sigma t)
		    else raise e)

	| IsApp (f,la) -> 
	    (check_rec_call env n lst f) &&
	    (array_for_all (check_rec_call env n lst) la) &&
            (List.for_all (check_rec_call env n lst) l)

	| IsCoFix (i,(_,typarray,bodies as recdef)) ->
	    let nbfix = Array.length typarray in
	    let env' = push_rec_types recdef env in
	    (array_for_all (check_rec_call env n lst) typarray) &&
            (List.for_all (check_rec_call env n lst) l) &&
	    (array_for_all
	       (check_rec_call env' (n+nbfix) (map_lift_fst_n nbfix lst))
	       bodies)

	| IsEvar (_,la) -> 
	    (array_for_all (check_rec_call env n lst) la) &&
            (List.for_all (check_rec_call env n lst) l)

	| IsMeta _ -> true

	| IsVar _ | IsSort _ ->  List.for_all (check_rec_call env n lst) l
     )

     and check_rec_call_fix_body env n lst decr recArgsDecrArg body =
	if decr = 0 then
	  check_rec_call env n ((1,recArgsDecrArg)::lst) body
	else
	  match kind_of_term body with
	    | IsLambda (x,a,b) ->
		(check_rec_call env n lst a) &
		(check_rec_call_fix_body
		   (push_rel_assum (x, a) env) (n+1)
		   (map_lift_fst lst) (decr-1) recArgsDecrArg b)
	    | _ -> anomaly "Not enough abstractions in fix body"
    
   in 
   check_rec_call env' 1 [] d)

(* vargs is supposed to be built from A1;..Ak;[f1]..[fk][|d1;..;dk|]
and vdeft is [|t1;..;tk|] such that f1:A1,..,fk:Ak |- di:ti
nvect is [|n1;..;nk|] which gives for each recursive definition 
the inductive-decreasing index 
the function checks the convertibility of ti with Ai *)

let check_fix env sigma ((nvect,bodynum),(names,types,bodies as recdef)) =
  let nbfix = Array.length bodies in 
  if nbfix = 0
    or Array.length nvect <> nbfix 
    or Array.length types <> nbfix
    or Array.length names <> nbfix
    or bodynum < 0
    or bodynum >= nbfix
  then anomaly "Ill-formed fix term";
  for i = 0 to nbfix - 1 do
    let fixenv = push_rec_types recdef env in
    try
      let _ = check_subterm_rec_meta fixenv sigma nvect nvect.(i) bodies.(i)
      in ()
    with FixGuardError err ->
      error_ill_formed_rec_body	CCI fixenv err names i bodies
  done 

(*
let cfkey = Profile.declare_profile "check_fix";;
let check_fix env sigma fix = Profile.profile3 cfkey check_fix env sigma fix;;
*)

(* Co-fixpoints. *)

exception CoFixGuardError of guard_error

let check_guard_rec_meta env sigma nbfix def deftype = 
  let rec codomain_is_coind env c =
    let b = whd_betadeltaiota env sigma (strip_outer_cast c) in
    match kind_of_term b with
      | IsProd (x,a,b) ->
	  codomain_is_coind (push_rel_assum (x, a) env) b 
      | _ -> 
	  try
	    find_coinductive env sigma b
          with Induc ->
	    raise (CoFixGuardError (CodomainNotInductiveType b))
  in
  let (mind, _) = codomain_is_coind env deftype in
  let ((sp,tyi),_) = mind in
  let lvlra = mis_recargs (lookup_mind_specif mind env) in
  let vlra = lvlra.(tyi) in  
  let rec check_rec_call env alreadygrd n vlra  t =
    if noccur_with_meta n nbfix t then
      true 
    else
      let c,args = whd_betadeltaiota_stack env sigma t in
      match kind_of_term c with 
	| IsMeta _ -> true
	      
	| IsRel p -> 
             if n <= p && p < n+nbfix then
	       (* recursive call *)
               if alreadygrd then
		 if List.for_all (noccur_with_meta n nbfix) args then
		   true
		 else 
		   raise (CoFixGuardError NestedRecursiveOccurrences)
               else 
		 raise (CoFixGuardError (UnguardedRecursiveCall t))
             else  
	       error "check_guard_rec_meta: ???"  (* ??? *)
		 
	| IsMutConstruct ((_,i as cstr_sp),l)  ->
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
                            (check_rec_call env true n newvlra t) &&
                            (process_args_of_constr lr lrar)
			    
                       |  (Imbr((sp,i) as ind_sp,lrc)::lrar)  ->
			    let mis =
			      lookup_mind_specif (ind_sp,[||]) env in
                            let sprecargs = mis_recargs mis in
                            let lc = (Array.map 
                                        (List.map 
                                           (instantiate_recarg sp lrc))
                                        sprecargs.(i))
                            in (check_rec_call env true n lc t) &
                               (process_args_of_constr lr lrar)
				 
                       |  _::lrar  -> 
                            if (noccur_with_meta n nbfix t) 
                            then (process_args_of_constr lr lrar)
                            else raise (CoFixGuardError
					  (RecCallInNonRecArgOfConstructor t)))
            in (process_args_of_constr realargs lra)
		 
		 
	| IsLambda (x,a,b) ->
	     assert (args = []);
            if (noccur_with_meta n nbfix a) then
              check_rec_call (push_rel_assum (x, a) env)
		alreadygrd (n+1)  vlra b
            else 
	      raise (CoFixGuardError (RecCallInTypeOfAbstraction t))
	      
	| IsCoFix (j,(_,varit,vdefs as recdef)) ->
            if (List.for_all (noccur_with_meta n nbfix) args)
            then 
              let nbfix = Array.length vdefs in
	      if (array_for_all (noccur_with_meta n nbfix) varit) then
		let env' = push_rec_types recdef env in
		(array_for_all
		   (check_rec_call env' alreadygrd (n+1) vlra) vdefs)
		&&
		(List.for_all (check_rec_call env alreadygrd (n+1) vlra) args) 
              else 
		raise (CoFixGuardError (RecCallInTypeOfDef c))
	    else
	      raise (CoFixGuardError (UnguardedRecursiveCall c))

	| IsMutCase (_,p,tm,vrest) ->
            if (noccur_with_meta n nbfix p) then
              if (noccur_with_meta n nbfix tm) then
		if (List.for_all (noccur_with_meta n nbfix) args) then
		  (array_for_all (check_rec_call env alreadygrd n vlra) vrest)
		else 
		  raise (CoFixGuardError (RecCallInCaseFun c))
              else 
		raise (CoFixGuardError (RecCallInCaseArg c))
            else 
	      raise (CoFixGuardError (RecCallInCasePred c))
              
	| _    -> raise (CoFixGuardError NotGuardedForm)
	      
  in 
  check_rec_call env false 1 vlra def

(* The  function which checks that the whole block of definitions 
   satisfies the guarded condition *)

let check_cofix env sigma (bodynum,(names,types,bodies as recdef)) = 
  let nbfix = Array.length bodies in 
  for i = 0 to nbfix-1 do
    let fixenv = push_rec_types recdef env in
    try 
      let _ = check_guard_rec_meta fixenv sigma nbfix bodies.(i) types.(i)
      in ()
    with CoFixGuardError err -> 
      error_ill_formed_rec_body CCI fixenv err names i bodies
  done

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
      (Array.map (fun j -> body_of_type j.uj_type) vdefj)
      (Array.map body_of_type lar)
  with IllBranch i ->
    error_ill_typed_rec_body CCI env i lna vdefj lar


(* A function which checks that a term well typed verifies both
   syntaxic conditions *)

let control_only_guard env sigma = 
  let rec control_rec c = match kind_of_term c with
    | IsRel _ | IsVar _    -> ()
    | IsSort _ | IsMeta _ -> ()
    | IsCoFix (_,(_,tys,bds) as cofix) ->
	check_cofix env sigma cofix;
	Array.iter control_rec tys;
	Array.iter control_rec bds;
    | IsFix (_,(_,tys,bds) as fix) ->
	check_fix env sigma fix; 
	Array.iter control_rec tys;
	Array.iter control_rec bds;
    | IsMutCase(_,p,c,b) ->control_rec p;control_rec c;Array.iter control_rec b
    | IsMutInd (_,cl)       -> Array.iter control_rec cl
    | IsMutConstruct (_,cl) -> Array.iter control_rec cl
    | IsConst (_,cl)        -> Array.iter control_rec cl
    | IsEvar (_,cl)         -> Array.iter control_rec cl
    | IsApp (_,cl)         -> Array.iter control_rec cl
    | IsCast (c1,c2)       -> control_rec c1; control_rec c2
    | IsProd (_,c1,c2)     -> control_rec c1; control_rec c2
    | IsLambda (_,c1,c2)   -> control_rec c1; control_rec c2
    | IsLetIn (_,c1,c2,c3) -> control_rec c1; control_rec c2; control_rec c3
  in 
  control_rec 
