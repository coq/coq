
(* $Id$ *)

open Pp
open Util
open Names
open Univ
open Generic
open Term
open Constant
open Inductive
open Sign
open Environ
open Reduction
open Instantiate
open Type_errors

let make_judge v tj =
  { uj_val = v;
    uj_type = tj.body;
    uj_kind= DOP0 (Sort tj.typ) }

let j_val_only j = j.uj_val
(* Faut-il caster ? *)
let j_val = j_val_only

let j_val_cast j = mkCast j.uj_val j.uj_type

let typed_type_of_judgment env sigma j =
  match whd_betadeltaiota env sigma j.uj_kind with
    | DOP0(Sort s) -> { body = j.uj_type; typ = s }
    | _ -> error_not_type CCI env j.uj_type

let assumption_of_judgment env sigma j =
  match whd_betadeltaiota env sigma j.uj_type with
    | DOP0(Sort s) -> { body = j.uj_val; typ = s }
    | _ -> error_assumption CCI env j.uj_val

(* Type of a de Bruijn index. *)
	  
let relative env n = 
  try
    let (_,typ) = lookup_rel n env in
    { uj_val  = Rel n;
      uj_type = lift n typ.body;
      uj_kind = DOP0 (Sort typ.typ) }
  with Not_found -> 
    error_unbound_rel CCI env n

(* Management of context of variables. *)

(* Checks if a context of variable is included in another one. *)

let hyps_inclusion env sigma (idl1,tyl1) (idl2,tyl2) =
  let rec aux = function
    | ([], [], _, _) -> true
    | (_, _, [], []) -> false
    | ((id1::idl1), (ty1::tyl1), idl2, tyl2) ->
        let rec search = function
          | ([], []) -> false
          | ((id2::idl2), (ty2::tyl2)) ->
              if id1 = id2 then
		(is_conv env sigma (body_of_type ty1) (body_of_type ty2))
		& aux (idl1,tyl1,idl2,tyl2)
              else 
		search (idl2,tyl2)
          | (_, _) -> invalid_arg "hyps_inclusion"
        in 
	search (idl2,tyl2)
    | (_, _, _, _) -> invalid_arg "hyps_inclusion"
  in
  aux (idl1,tyl1,idl2,tyl2) 

(* Checks if the given context of variables [hyps] is included in the
   current context of [env]. *)

let construct_reference id env sigma hyps =
  let hyps' = var_context env in
  if hyps_inclusion env sigma hyps hyps' then
    Array.of_list (List.map (fun id -> VAR id) (ids_of_sign hyps))
  else 
    error_reference_variables CCI env id

let check_hyps id env sigma hyps =
  let hyps' = var_context env in
  if not (hyps_inclusion env sigma hyps hyps') then
    error_reference_variables CCI env id

(* Instantiation of terms on real arguments. *)

let type_of_constant env sigma c =
  let (sp,args) = destConst c in
  let cb = lookup_constant sp env in
  let hyps = cb.const_hyps in
  check_hyps (basename sp) env sigma hyps;
  instantiate_type (ids_of_sign hyps) cb.const_type (Array.to_list args)

(* Inductive types. *)

let instantiate_arity mis =
  let ids = ids_of_sign mis.mis_mib.mind_hyps in
  let args = Array.to_list mis.mis_args in 
  let arity = mis.mis_mip.mind_arity in
  { body = instantiate_constr ids arity.body args;
    typ = arity.typ }

let type_of_inductive env sigma i =
  let mis = lookup_mind_specif i env in
  let hyps = mis.mis_mib.mind_hyps in
  check_hyps (basename mis.mis_sp) env sigma hyps;
  instantiate_arity mis

(* Constructors. *)

let instantiate_lc mis =
  let hyps = mis.mis_mib.mind_hyps in
  let lc = mis.mis_mip.mind_lc in
  instantiate_constr (ids_of_sign hyps) lc (Array.to_list mis.mis_args)

let type_of_constructor env sigma c =
  let (sp,i,j,args) = destMutConstruct c in
  let mind = DOPN (MutInd (sp,i), args) in
  let recmind = check_mrectype_spec env sigma mind in
  let mis = lookup_mind_specif recmind env in
  check_hyps (basename mis.mis_sp) env sigma (mis.mis_mib.mind_hyps);
  let specif = instantiate_lc mis in
  let make_ik k = DOPN (MutInd (mis.mis_sp,k), mis.mis_args) in
  if j > mis_nconstr mis then
    anomaly "type_of_constructor"
  else
    sAPPViList (j-1) specif (list_tabulate make_ik (mis_ntypes mis))

(* gives the vector of constructors and of 
   types of constructors of an inductive definition 
   correctly instanciated *)

let mis_type_mconstructs mis =
  let specif = instantiate_lc mis
  and ntypes = mis_ntypes mis
  and nconstr = mis_nconstr mis in
  let make_ik k = DOPN (MutInd (mis.mis_sp,k), mis.mis_args) 
  and make_ck k = 
    DOPN (MutConstruct ((mis.mis_sp,mis.mis_tyi),k+1), mis.mis_args) 
  in
  (Array.init nconstr make_ck, 
   sAPPVList specif (list_tabulate make_ik ntypes))

let type_mconstructs env sigma mind =
  let redmind = check_mrectype_spec env sigma mind in
  let mis = lookup_mind_specif redmind env in 
  mis_type_mconstructs mis

let mis_type_mconstruct i mispec =
  let specif = instantiate_lc mispec
  and ntypes = mis_ntypes mispec
  and nconstr = mis_nconstr mispec in
  let make_Ik k = DOPN(MutInd(mispec.mis_sp,k),mispec.mis_args) in 
  if i > nconstr then error "Not enough constructors in the type";
  sAPPViList (i-1) specif (list_tabulate make_Ik ntypes)

let type_mconstruct env sigma i mind =
  let redmind = check_mrectype_spec env sigma mind in
  let (sp,tyi,args) = destMutInd redmind in
  let mispec = lookup_mind_specif redmind env in 
  mis_type_mconstruct i mispec

let type_inst_construct env sigma i mind = 
  try 
    let (mI,largs) = find_mrectype env sigma mind in 
    let mispec = lookup_mind_specif mI env in 
    let nparams = mis_nparams mispec in 
    let tc = mis_type_mconstruct i mispec in
    let (globargs,_) = list_chop nparams largs in
    hnf_prod_applist env sigma "Typing.type_construct" tc globargs
  with Induc -> 
    error_not_inductive CCI env mind

let type_of_existential env sigma c =
  let (ev,args) = destEvar c in
  let evi = Evd.map sigma ev in
  let hyps = var_context evi.Evd.evar_env in
  let id = id_of_string ("?" ^ string_of_int ev) in
  check_hyps id env sigma hyps;
  instantiate_constr (ids_of_sign hyps) evi.Evd.evar_concl (Array.to_list args)


(* Case. *)

let rec sort_of_arity env sigma c =
  match whd_betadeltaiota env sigma c with
    | DOP0(Sort( _)) as c' -> c'
    | DOP2(Prod,_,DLAM(_,c2)) -> sort_of_arity env sigma c2
    | _ -> invalid_arg "sort_of_arity"

let make_arity_dep env sigma k = 
  let rec mrec c m = match whd_betadeltaiota env sigma c with 
    | DOP0(Sort _) -> mkArrow m k
    | DOP2(Prod,b,DLAM(n,c_0)) ->
        prod_name env (n,b,mrec c_0 (applist(lift 1 m,[Rel 1])))
    | _ -> invalid_arg "make_arity_dep"
  in 
  mrec

let make_arity_nodep env sigma k = 
  let rec mrec c = match whd_betadeltaiota env sigma c with 
    | DOP0(Sort _) -> k
    | DOP2(Prod,b,DLAM(x,c_0)) -> DOP2(Prod,b,DLAM(x,mrec c_0))
    | _ -> invalid_arg "make_arity_nodep"
  in 
  mrec

let error_elim_expln env sigma kp ki =
  if is_info_sort env sigma kp && not (is_info_sort env sigma ki) then
    "non-informative objects may not construct informative ones."
  else 
    match (kp,ki) with 
      | (DOP0(Sort (Type _)), DOP0(Sort (Prop _))) ->
          "strong elimination on non-small inductive types leads to paradoxes."
      | _ -> "wrong arity"

exception Arity of (constr * constr * string) option

let is_correct_arity env sigma kelim (c,p) = 
  let rec srec ind (pt,t) =
    try 
      (match whd_betadeltaiota env sigma pt, whd_betadeltaiota env sigma t with
	 | DOP2(Prod,a1,DLAM(_,a2)), DOP2(Prod,a1',DLAM(_,a2')) ->
             if is_conv env sigma a1 a1' then
               srec (applist(lift 1 ind,[Rel 1])) (a2,a2') 
             else 
	       raise (Arity None)
	 | DOP2(Prod,a1,DLAM(_,a2)), ki -> 
             let k = whd_betadeltaiota env sigma a2 in 
             let ksort = (match k with DOP0(Sort s) -> s 
			    | _ -> raise (Arity None)) in
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
	       raise (Arity (Some(k,ki,error_elim_expln env sigma k ki))))
    with Arity kinds ->
      let listarity =
	(List.map 
	   (fun s -> make_arity_dep env sigma (DOP0(Sort s)) t ind) kelim)
	@(List.map 
	    (fun s -> make_arity_nodep env sigma (DOP0(Sort s)) t) kelim)
      in 
      error_elim_arity CCI env ind listarity c p pt kinds
  in 
  srec 

let cast_instantiate_arity mis =
  let tty = instantiate_arity mis in
  DOP2 (Cast, tty.body, DOP0 (Sort tty.typ))

let find_case_dep_nparams env sigma (c,p) (mind,largs) typP =    
  let mis = lookup_mind_specif mind env in 
  let nparams = mis_nparams mis
  and kelim = mis_kelim mis 
  and t = cast_instantiate_arity mis in 
  let (globargs,la) = list_chop nparams largs in
  let glob_t = hnf_prod_applist env sigma "find_elim_boolean" t globargs in
  let arity = applist(mind,globargs) in
  let (dep,_) = is_correct_arity env sigma kelim (c,p) arity (typP,glob_t) in
  (dep, (nparams, globargs,la))

let type_one_branch_dep env sigma (nparams,globargs,p) co t = 
  let rec typrec n c =
    match whd_betadeltaiota env sigma c with
      | DOP2(Prod,a1,DLAM(x,a2)) -> prod_name env (x,a1,typrec (n+1) a2)
      | x -> let lAV = destAppL (ensure_appl x) in
             let (_,vargs) = array_chop (nparams+1) lAV in
             applist 
               (appvect ((lift n p),vargs),
		[applist(co,((List.map (lift n) globargs)@(rel_list 0 n)))])
  in 
  typrec 0 (hnf_prod_applist env sigma "type_case" t globargs)

let type_one_branch_nodep env sigma (nparams,globargs,p) t = 
  let rec typrec n c =
    match whd_betadeltaiota env sigma c with 
      | DOP2(Prod,a1,DLAM(x,a2)) -> DOP2(Prod,a1,DLAM(x,typrec (n+1) a2))
      | x -> let lAV = destAppL(ensure_appl x) in
             let (_,vargs) = array_chop (nparams+1) lAV in
             appvect (lift n p,vargs)
  in 
  typrec 0 (hnf_prod_applist env sigma "type_case" t globargs)

(* type_case_branches type un <p>Case c of ... end 
   ct = type de c, si inductif il a la forme APP(mI,largs), sinon raise Induc
   pt = sorte de p
   type_case_branches retourne (lb, lr); lb est le vecteur des types
   attendus dans les branches du Case; lr est le type attendu du resultat
 *)

let type_case_branches env sigma ct pt p c =
  try
    let ((mI,largs) as indt) = find_mrectype env sigma ct in
    let (dep,(nparams,globargs,la)) =
      find_case_dep_nparams env sigma (c,p) indt pt
    in
    let (lconstruct,ltypconstr) = type_mconstructs env sigma mI in
    if dep then 
      (mI, 
       array_map2 (type_one_branch_dep env sigma (nparams,globargs,p))
         lconstruct ltypconstr,
         beta_applist (p,(la@[c])))
    else 
      (mI,
       Array.map (type_one_branch_nodep env sigma (nparams,globargs,p)) 
         ltypconstr,
         beta_applist (p,la))
  with Induc -> 
    error_case_not_inductive CCI env c ct

let check_branches_message env sigma (c,ct) (explft,lft) = 
  let n = Array.length explft 
  and expn = Array.length lft in
  if n<>expn then error_number_branches CCI env c ct expn;
  for i = 0 to n-1 do
    if not (is_conv_leq env sigma lft.(i) (explft.(i))) then
      error_ill_formed_branch CCI env c i (nf_betaiota env sigma lft.(i))
	(nf_betaiota env sigma explft.(i))
  done

let type_of_case env sigma pj cj lfj =
  let lft = Array.map (fun j -> j.uj_type) lfj in
  let (mind,bty,rslty) =
    type_case_branches env sigma cj.uj_type pj.uj_type pj.uj_val cj.uj_val in
  let kind = sort_of_arity env sigma pj.uj_type in
  check_branches_message env sigma (cj.uj_val,cj.uj_type) (bty,lft);
  { uj_val  = 
      mkMutCaseA (ci_of_mind mind) (j_val pj) (j_val cj) (Array.map j_val lfj);
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

let abs_rel env sigma name var j =
  let rngtyp = whd_betadeltaiota env sigma j.uj_kind in
  let cvar = incast_type var in
  let (s,cst) = sort_of_product var.typ (destSort rngtyp) (universes env) in
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
	  let (s',g) = sort_of_product var.typ s (universes env) in
          let res_type = mkSort s' in
	  let (res_kind,g') = type_of_sort res_type in
          { uj_val = 
	      mkProd name (mkCast var.body (mkSort var.typ)) (j_val_cast j);
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
  let rec apply_rec typ cst = function
    | [] -> 
	{ uj_val  = applist (j_val_only funj, List.map j_val_only argjl);
          uj_type = typ;
          uj_kind = funj.uj_kind },
	cst
    | hj::restjl ->
        match whd_betadeltaiota env sigma typ with
          | DOP2(Prod,c1,DLAM(_,c2)) ->
              if nocheck then
                apply_rec (subst1 hj.uj_val c2) cst restjl
	      else 
		(try 
		   let c = conv_leq env sigma hj.uj_type c1 in
		   let cst' = Constraint.union cst c in
		   apply_rec (subst1 hj.uj_val c2) cst' restjl
		 with NotConvertible -> 
		   error_cant_apply CCI env "Type Error" funj argjl)
          | _ ->
              error_cant_apply CCI env "Non-functional construction" funj argjl
  in 
  apply_rec funj.uj_type Constraint.empty argjl


(* Fixpoints. *)

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

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
    | Mrec(j)        -> Imbr(sp,j,lrc)
    | Imbr(sp1,k,l)  -> Imbr(sp1,k, List.map (instantiate_recarg sp lrc) l)
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
      | (Imbr(sp,i,lrc)::lr,DOP2(Lambda,_,DLAM(_,b))) -> 
          let l' = map_lift_fst l in
          let sprecargs = 
	    mis_recargs (lookup_mind_specif (mkMutInd sp i [||]) env) in
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
   let (mI, largs) = 
     (try find_minductype env sigma c 
      with Induc -> error "Recursive definition on a non inductive type") in
   let (sp,tyi,_) = destMutInd mI in
   let mind_recvec = mis_recargs (lookup_mind_specif mI env) in 
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

let check_fix env sigma = function
  | DOPN(Fix(nvect,j),vargs) -> 
      let nbfix = let nv = Array.length vargs in 
      if nv < 2 then error "Ill-formed recursive definition" else nv-1 in
      let varit = Array.sub vargs 0 nbfix in
      let ldef = array_last vargs in
      let ln = Array.length nvect 
      and la = Array.length varit in
      if ln <> la then 
	error "Ill-formed fix term"
      else 
	let (lna,vdefs) = decomp_DLAMV_name ln ldef in 
	let vlna = Array.of_list lna in
	let check_type i = 
	  try
	    let _ = 
	      check_subterm_rec_meta env sigma nvect nvect.(i) vdefs.(i) in 
	    ()
	  with UserError (s,str) ->
	    error_ill_formed_rec_body CCI env str lna i vdefs 
	in
	for i = 0 to ln-1 do check_type i done 

  | _ -> assert false

(* Co-fixpoints. *)

let mind_nparams env i =
  let mis = lookup_mind_specif i env in mis.mis_mib.mind_nparams

let check_guard_rec_meta env sigma nbfix def deftype = 
  let rec codomain_is_coind c  =
    match whd_betadeltaiota env sigma (strip_outer_cast c) with
      | DOP2(Prod,a,DLAM(_,b)) -> codomain_is_coind b 
      | b  -> 
	  (try find_mcoinductype env sigma b
           with 
	     | Induc -> error "The codomain is not a coinductive type"
	     | _ -> error "Type of Cofix function not as expected")
  in
  let (mI, _) = codomain_is_coind deftype in
  let (sp,tyi,_) = destMutInd mI in
  let lvlra = (mis_recargs (lookup_mind_specif mI env)) in
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
		 
	| (DOPN ((MutConstruct((x,y),i)),l), args)  ->
            let lra =vlra.(i-1) in 
            let mI = DOPN(MutInd(x,y),l) in
            let _,realargs = list_chop (mind_nparams env mI) args in
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
			    
                       |  (Imbr(sp,i,lrc)::lrar)  ->
			    let mis =
			      lookup_mind_specif (mkMutInd sp i [||]) env in
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
	      
	| (DOPN(CoFix(j),vargs),l) -> 
          if  (List.for_all (noccur_with_meta n nbfix) l)
          then 
            let nbfix = let nv = Array.length vargs in 
            if nv < 2 then
              error "Ill-formed recursive definition" 
            else 
	      nv-1 
	    in
            let varit = Array.sub vargs 0 nbfix in
            let ldef = array_last vargs in
            let la = Array.length varit in
            let (lna,vdefs) = decomp_DLAMV_name la ldef in
            let vlna = Array.of_list lna 
            in 
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


(* Checks the type of a (co)fixpoint.
   Fix and CoFix are typed the same way; only the guard condition differs. *)

exception IllBranch of int

let type_fixpoint env sigma lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Array.length lar = lt);
  try
    conv_forall2_i
      (fun i e def ar -> 
	 try conv_leq e def (lift lt ar) 
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
	check_cofix env sigma cofix; 
	Array.iter control_rec cl
    | DOPN(Fix(_),cl) as fix  -> 
	check_fix env sigma fix; 
        Array.iter control_rec cl
    | DOPN(_,cl)    -> Array.iter control_rec cl
    | DOPL(_,cl)    -> List.iter control_rec cl
    | DOP1(_,c)     -> control_rec c
    | DOP2(_,c1,c2) -> control_rec c1; control_rec c2
    | DLAM(_,c)     -> control_rec c
    | DLAMV(_,v)    -> Array.iter control_rec v
  in 
  control_rec 
