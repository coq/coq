
(* $Id$ *)

open Pp
open Util
open Names
open Univ
open Generic
open Term
open Declarations
open Sign
open Environ
open Reduction
open Inductive

open Type_errors

let make_judge v tj =
  { uj_val = v;
    uj_type = body_of_type tj;
    uj_kind= DOP0 (Sort (level_of_type tj)) }

let j_val_only j = j.uj_val
(* Faut-il caster ? *)
let j_val = j_val_only

let j_val_cast j = mkCast j.uj_val j.uj_type

let typed_type_of_judgment env sigma j =
  match whd_betadeltaiota env sigma j.uj_kind with
    | DOP0(Sort s) -> make_typed j.uj_type s
    | _ -> error_not_type CCI env j.uj_type


let assumption_of_judgment env sigma j =
  match whd_betadeltaiota env sigma j.uj_type with
    | DOP0(Sort s) -> make_typed j.uj_val s
    | _ -> error_assumption CCI env j.uj_val

(* Type of a de Bruijn index. *)
	  
let relative env n = 
  try
    let (_,typ) = lookup_rel n env in
    { uj_val  = Rel n;
      uj_type = lift n (body_of_type typ);
      uj_kind = DOP0 (Sort (level_of_type typ)) }
  with Not_found -> 
    error_unbound_rel CCI env n

(* Management of context of variables. *)

(* Checks if a context of variable is included in another one. *)

let rec hyps_inclusion env sigma sign1 sign2 =
  if isnull_sign sign1 then true
  else
    let (id1,ty1) = hd_sign sign1 in
    let rec search sign2 =
      if isnull_sign sign2 then false
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

(* Checks if the given context of variables [hyps] is included in the
   current context of [env]. *)

let check_hyps id env sigma hyps =
  let hyps' = var_context env in
  if not (hyps_inclusion env sigma hyps hyps') then
    error_reference_variables CCI env id

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

let type_mconstructs env sigma mind =
  mis_type_mconstructs (lookup_mind_specif mind env)

let type_mconstruct env sigma i mind =
  mis_type_mconstruct i (lookup_mind_specif mind env)

let type_of_constructor env sigma cstr =
  type_mconstruct env sigma
    (index_of_constructor cstr)
    (inductive_of_constructor cstr)

let type_inst_construct i (IndFamily (mis,globargs)) =
  let tc = mis_type_mconstruct i mis in
  prod_applist tc globargs

let type_of_existential env sigma c =
  Instantiate.existential_type sigma (destEvar c)

(* Case. *)

let rec mysort_of_arity env sigma c =
  match whd_betadeltaiota env sigma c with
    | DOP0(Sort( _)) as c' -> c'
    | DOP2(Prod,_,DLAM(_,c2)) -> mysort_of_arity env sigma c2
    | _ -> invalid_arg "mysort_of_arity"

let error_elim_expln env sigma kp ki =
  if is_info_sort env sigma kp && not (is_info_sort env sigma ki) then
    "non-informative objects may not construct informative ones."
  else 
    match (kp,ki) with 
      | (DOP0(Sort (Type _)), DOP0(Sort (Prop _))) ->
          "strong elimination on non-small inductive types leads to paradoxes."
      | _ -> "wrong arity"

exception Arity of (constr * constr * string) option

let is_correct_arity env sigma kelim (c,p) indf (pt,t) = 
  let rec srec (pt,t) =
    match whd_betadeltaiota env sigma pt, whd_betadeltaiota env sigma t with
      | DOP2(Prod,a1,DLAM(_,a2)), DOP2(Prod,a1',DLAM(_,a2')) ->
          if is_conv env sigma a1 a1' then
            srec (a2,a2') 
          else 
	    raise (Arity None)
      | DOP2(Prod,a1,DLAM(_,a2)), ki -> 
          let k = whd_betadeltaiota env sigma a2 in 
          let ksort = (match k with DOP0(Sort s) -> s 
			 | _ -> raise (Arity None)) in
	  let ind = build_dependent_inductive indf in
          if is_conv env sigma a1 ind then
            if List.exists (base_sort_cmp CONV ksort) kelim then
	      (true,k)
            else 
	      raise (Arity (Some(k,ki,error_elim_expln env sigma k ki)))
	  else 
	    raise (Arity None)
      | k, DOP2(Prod,_,_) ->
	  raise (Arity None)
      | k, ki -> 
	  let ksort = (match k with DOP0(Sort s) -> s 
                         | _ ->  raise (Arity None)) in
          if List.exists (base_sort_cmp CONV ksort) kelim then 
	    false,k
          else 
	    raise (Arity (Some(k,ki,error_elim_expln env sigma k ki)))
in 
  try srec (pt,t)
  with Arity kinds ->
    let listarity =
      (List.map (make_arity env sigma true indf) kelim)
      @(List.map (make_arity env sigma false indf) kelim)
    in 
    let ind = mis_inductive (fst (dest_ind_family indf)) in
    error_elim_arity CCI env ind listarity c p pt kinds


let find_case_dep_nparams env sigma (c,p) (IndFamily (mis,_) as indf) typP =
  let kelim = mis_kelim mis in
  let arsign,s = get_arity env sigma indf in
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
  let lft = Array.map (fun j -> j.uj_type) lfj in
  let indspec =
    try find_inductive env sigma cj.uj_type
    with Induc -> error_case_not_inductive CCI env cj.uj_val cj.uj_type in
  let (bty,rslty) =
    type_case_branches env sigma indspec pj.uj_type pj.uj_val cj.uj_val in
  let kind = mysort_of_arity env sigma pj.uj_type in
  check_branches_message env sigma (cj.uj_val,cj.uj_type) (bty,lft);
  { uj_val  = mkMutCaseA ci (j_val pj) (j_val cj) (Array.map j_val lfj);
    uj_type = rslty;
    uj_kind = kind }

(* Prop and Set *)

let judge_of_prop =
  { uj_val = DOP0(Sort prop);
    uj_type = DOP0(Sort type_0);
    uj_kind = DOP0(Sort type_1) }

let judge_of_set =
  { uj_val = DOP0(Sort spec);
    uj_type = DOP0(Sort type_0);
    uj_kind = DOP0(Sort type_1) }

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

(* Type of Type(i). *)

let judge_of_type u =
  let (uu,uuu,c) = super_super u in
  { uj_val = DOP0 (Sort (Type u));
    uj_type = DOP0 (Sort (Type uu));
    uj_kind = DOP0 (Sort (Type uuu)) },
  c

let type_of_sort c =
  match c with
    | DOP0 (Sort (Type u)) -> let (uu,cst) = super u in mkType uu, cst
    | DOP0 (Sort (Prop _)) -> mkType prop_univ, Constraint.empty
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

let abs_rel env sigma name var j =
  let rngtyp = whd_betadeltaiota env sigma j.uj_kind in
  let cvar = incast_type var in
  let (s,cst) =
    sort_of_product (level_of_type var) (destSort rngtyp) (universes env) in
  { uj_val = mkLambda name cvar (j_val j);
    uj_type = mkProd name cvar j.uj_type;
    uj_kind = mkSort s },
  cst

(* Type of a product. *)

let gen_rel env sigma name var j =
  let jtyp = whd_betadeltaiota env sigma j.uj_type in
  let jkind = whd_betadeltaiota env sigma j.uj_kind in
  let j = { uj_val = j.uj_val; uj_type = jtyp; uj_kind = jkind } in
  if isprop jkind then 
    error "Proof objects can only be abstracted" 
  else
    match jtyp with
      | DOP0(Sort s) ->
	  let (s',g) = sort_of_product (level_of_type var) s (universes env) in
          let res_type = mkSort s' in
	  let (res_kind,g') = type_of_sort res_type in
          { uj_val = 
	      mkProd name (incast_type var) (j_val_cast j);
            uj_type = res_type;
            uj_kind = res_kind }, g'
      | _ -> 
	  error_generalization CCI env (name,var) j.uj_val

(* Type of a cast. *)
	    
let cast_rel env sigma cj tj =
  if is_conv_leq env sigma cj.uj_type tj.uj_val then
    { uj_val = j_val_only cj;
      uj_type = tj.uj_val;
      uj_kind = whd_betadeltaiota env sigma tj.uj_type }
  else 
    error_actual_type CCI env cj.uj_val cj.uj_type tj.uj_val

(* Type of an application. *)

let apply_rel_list env sigma nocheck argjl funj =
  let rec apply_rec n typ cst = function
    | [] -> 
	{ uj_val  = applist (j_val_only funj, List.map j_val_only argjl);
          uj_type = typ;
          uj_kind = funj.uj_kind },
	cst
    | hj::restjl ->
        match whd_betadeltaiota env sigma typ with
          | DOP2(Prod,c1,DLAM(_,c2)) ->
              if nocheck then
                apply_rec (n+1) (subst1 hj.uj_val c2) cst restjl
	      else 
		(try 
		   let c = conv_leq env sigma hj.uj_type c1 in
		   let cst' = Constraint.union cst c in
		   apply_rec (n+1) (subst1 hj.uj_val c2) cst' restjl
		 with NotConvertible -> 
		   error_cant_apply_bad_type CCI env (n,hj.uj_type,c1)
		     funj argjl)
          | _ ->
	      error_cant_apply_not_functional CCI env funj argjl
  in 
  apply_rec 1 funj.uj_type Constraint.empty argjl


(* Fixpoints. *)

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

exception Occur
let noccur_with_meta n m term = 
  let rec occur_rec n = function
    | Rel p -> if n<=p & p<n+m then raise Occur
    | VAR _ -> ()
    | DOPN(AppL,cl) ->
	(match strip_outer_cast cl.(0) with
           | DOP0 (Meta _) -> ()
	   | _ -> Array.iter (occur_rec n) cl)
    | DOPN(Evar _, _) -> ()
    | DOPN(op,cl) -> Array.iter (occur_rec n) cl
    | DOPL(_,cl) -> List.iter (occur_rec n) cl
    | DOP0(_) -> ()
    | DOP1(_,c) -> occur_rec n c
    | DOP2(_,c1,c2) -> occur_rec n c1; occur_rec n c2
    | DLAM(_,c) -> occur_rec (n+1) c
    | DLAMV(_,v) -> Array.iter (occur_rec (n+1)) v
  in 
  try (occur_rec n term; true) with Occur -> false

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
    match (lrec,strip_outer_cast c) with
      | (Param(_)::lr,DOP2(Lambda,_,DLAM(_,b))) -> 
          let l' = map_lift_fst l in
          crec (n+1) l' (lr,b)
      | (Norec::lr,DOP2(Lambda,_,DLAM(_,b))) -> 
          let l' = map_lift_fst l in
          crec (n+1) l' (lr,b)
      | (Mrec(i)::lr,DOP2(Lambda,_,DLAM(_,b)))  -> 
          let l' = map_lift_fst l in
          crec (n+1) ((1,mind_recvec.(i))::l') (lr,b)
      | (Imbr((sp,i) as ind_sp,lrc)::lr,DOP2(Lambda,_,DLAM(_,b))) -> 
          let l' = map_lift_fst l in
          let sprecargs = 
	    mis_recargs (lookup_mind_specif (ind_sp,[||]) env) in
          let lc = 
	    Array.map (List.map (instantiate_recarg sp lrc)) sprecargs.(i)
	  in
          crec (n+1) ((1,lc)::l') (lr,b)
      | _,f_0 -> f n l f_0
  in 
  crec

let is_inst_var env sigma k c = 
  match whd_betadeltaiota_stack env sigma c [] with 
    | (Rel n,_) -> n=k
    | _ -> false

let is_subterm_specif env sigma lcx mind_recvec = 
  let rec crec n lst c = 
    match whd_betadeltaiota_stack env sigma c [] with 
      | ((Rel k),_) -> find_sorted_assoc k lst
      |  (DOPN(MutCase _,_) as x,_) ->
           let ( _,_,c,br) = destCase x in
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
	       
      | (DOPN(Fix(_),la) as mc,l) ->
          let (recindxs,i,typarray,funnames,bodies) = destUntypedFix mc in
          let nbfix   = List.length funnames in
          let decrArg = recindxs.(i) in 
          let theBody = bodies.(i)   in
          let (gamma,strippedBody) = decompose_lam_n (decrArg+1) theBody in
          let absTypes = List.map snd gamma in 
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
	    
      |  (DOP2(Lambda,_,DLAM(_,b)),[]) -> 
           let lst' = map_lift_fst lst in
           crec (n+1) lst' b

      (*** Experimental change *************************)
      | (DOP0(Meta _),_) -> [||]
      | _ -> raise Not_found
  in 
  crec

let is_subterm env sigma lcx mind_recvec n lst c = 
  try 
    let _ = is_subterm_specif env sigma lcx mind_recvec n lst c in true 
  with Not_found -> 
    false

(* Auxiliary function: it checks a condition f depending on a deBrujin
   index for a certain number of abstractions *)

let rec check_subterm_rec_meta env sigma vectn k def = 
  (k < 0) or
  (let nfi = Array.length vectn in 
   (* check fi does not appear in the k+1 first abstractions, 
      gives the type of the k+1-eme abstraction  *)
   let rec check_occur n def = 
     (match strip_outer_cast def with
	| DOP2(Lambda,a,DLAM(_,b)) -> 
	    if noccur_with_meta n nfi a then
              if n = k+1 then (a,b) else check_occur (n+1) b
            else 
	      error "Bad occurrence of recursive call"
        | _ -> error "Not enough abstractions in the definition") in
   let (c,d) = check_occur 1 def in 
   let ((sp,tyi),_ as mind, largs) = 
     (try find_minductype env sigma c 
      with Induc -> error "Recursive definition on a non inductive type") in
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
     (match whd_betadeltaiota_stack env sigma t [] with 
	| (Rel p,l) -> 
	    if n+k+1 <= p & p < n+k+nfi+1 then
	      (* recursive call *) 
	      let glob = nfi+n+k-p in  (* the index of the recursive call *) 
	      let np = vectn.(glob) in (* the decreasing arg of the rec call *)
	      if List.length l > np then 
		(match list_chop np l with
		     (la,(z::lrest)) -> 
	               if (is_subterm env sigma lcx mind_recvec n lst z) 
                       then List.for_all (check_rec_call n lst) (la@lrest)
                       else error "Recursive call applied to an illegal term"
		   | _ -> assert false)
	      else error  "Not enough arguments for the recursive call"
	    else List.for_all (check_rec_call n lst) l        
	| (DOPN(MutCase _,_) as mc,l) ->
            let (ci,p,c_0,lrest) = destCase mc in
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

	| (DOPN(Fix(_),la) as mc,l) ->
            (List.for_all (check_rec_call n lst) l) &&
            let (recindxs,i,typarray,funnames,bodies) = destUntypedFix mc in
            let nbfix = List.length funnames in
            let decrArg = recindxs.(i) in
            if (List.length l < (decrArg+1)) then
              (array_for_all (check_rec_call n lst) la)
            else 
              let theDecrArg  = List.nth l decrArg in
              let recArgsDecrArg = 
                try 
		  is_subterm_specif env sigma lcx mind_recvec n lst theDecrArg
	        with Not_found -> 
		  Array.create 0 [] 
              in 
	      if (Array.length recArgsDecrArg)=0 then
		array_for_all (check_rec_call n lst) la
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
		
		
	| (DOP2(_,a,b),l) -> 
	    (check_rec_call n lst a) &&
            (check_rec_call n lst b) &&
            (List.for_all (check_rec_call n lst) l)

	 | (DOPN(_,la),l) -> 
	     (array_for_all (check_rec_call n lst) la) &&
             (List.for_all (check_rec_call n lst) l)

	 | (DOP0 (Meta _),l) -> true

	 | (DLAM(_,t),l) -> 
	     (check_rec_call (n+1) (map_lift_fst lst) t) &&
             (List.for_all (check_rec_call n lst) l)

	 | (DLAMV(_,vt),l) -> 
	     (array_for_all (check_rec_call (n+1) (map_lift_fst lst)) vt) &&
             (List.for_all (check_rec_call n lst) l)

	 | (_,l) ->  List.for_all (check_rec_call n lst) l
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
  then error "Ill-formed fix term";
  for i = 0 to nbfix - 1 do
    try
      let _ = check_subterm_rec_meta env sigma nvect nvect.(i) bodies.(i) in ()
    with UserError (s,str) ->
      error_ill_formed_rec_body	CCI env str (List.rev names) i bodies
  done 

(* Co-fixpoints. *)

let check_guard_rec_meta env sigma nbfix def deftype = 
  let rec codomain_is_coind c  =
    match whd_betadeltaiota env sigma (strip_outer_cast c) with
      | DOP2(Prod,a,DLAM(_,b)) -> codomain_is_coind b 
      | b  -> 
	  (try find_mcoinductype env sigma b
           with 
	     | Induc -> error "The codomain is not a coinductive type"
(*	     | _ -> error "Type of Cofix function not as expected") ??? *) )
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
		   error "Nested recursive occurrences"
               else 
		 error "Unguarded recursive call"
             else  
	       error "check_guard_rec_meta: ???"
		 
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
                            else error "Recursive call inside a non-recursive argument of constructor")
            in (process_args_of_constr realargs lra)
		 
		 
	| (DOP2(Lambda,a,DLAM(_,b)),[]) -> 
            if (noccur_with_meta n nbfix a) then
              check_rec_call alreadygrd (n+1)  vlra b
            else 
	      error "Recursive call in the type of an abstraction"
	      
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
		error "Recursive call in the type of a declaration"
	    else error "Unguarded recursive call"

	| (DOPN(MutCase _,_) as mc,l) -> 
            let (_,p,c,vrest) = destCase mc in
            if (noccur_with_meta n nbfix p) then
              if (noccur_with_meta n nbfix c) then
		if (List.for_all (noccur_with_meta n nbfix) l) then
		  (array_for_all (check_rec_call alreadygrd n vlra) vrest)
		else 
		  error "Recursive call in the argument of a function defined by cases"        
              else 
		error "Recursive call in the argument of a case expression"
            else 
	      error "Recursive call in the type of a Case expression" 
              
	| _    -> error "Definition not in guarded form"
	      
  in 
  check_rec_call false 1 vlra def

(* The  function which checks that the whole block of definitions 
   satisfies the guarded condition *)

let check_cofix env sigma (bodynum,(types,names,bodies)) = 
  let nbfix = Array.length bodies in 
  for i = 0 to nbfix-1 do
    try 
      let _ = 
	check_guard_rec_meta env sigma nbfix bodies.(i) types.(i) in 
      ()
    with UserError (s,str) -> 
      error_ill_formed_rec_body CCI env str (List.rev names) i bodies
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
      (Array.map (fun j -> j.uj_type) vdefj) (Array.map body_of_type lar)
  with IllBranch i ->
    error_ill_typed_rec_body CCI env i lna vdefj lar


(* A function which checks that a term well typed verifies both
   syntaxic conditions *)

let control_only_guard env sigma = 
  let rec control_rec = function
    | Rel(p)        -> ()
    | VAR _         -> ()
    | DOP0(_)       -> ()
    | DOPN(CoFix(_),cl) as cofix ->
	check_cofix env sigma (destCoFix cofix); 
	Array.iter control_rec cl
    | DOPN(Fix(_),cl) as fix  -> 
	check_fix env sigma (destFix fix); 
        Array.iter control_rec cl
    | DOPN(_,cl)    -> Array.iter control_rec cl
    | DOPL(_,cl)    -> List.iter control_rec cl
    | DOP1(_,c)     -> control_rec c
    | DOP2(_,c1,c2) -> control_rec c1; control_rec c2
    | DLAM(_,c)     -> control_rec c
    | DLAMV(_,v)    -> Array.iter control_rec v
  in 
  control_rec 

(* [keep_hyps sign ids] keeps the part of the signature [sign] which 
   contains the variables of the set [ids], and recursively the variables 
   contained in the types of the needed variables. *)

let keep_hyps sign needed =
  rev_sign
    (fst (it_sign 
	    (fun ((hyps,globs) as sofar) id a ->
               if Idset.mem id globs then
                 (add_sign (id,a) hyps, 
		  Idset.union (global_vars_set (body_of_type a)) globs)
               else 
		 sofar) 
	    (nil_sign,needed) sign))
    
