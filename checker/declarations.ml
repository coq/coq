open Util
open Names
open Term
open Validate

(* Bytecode *)
type values
type reloc_table
type to_patch_substituted
(*Retroknowledge *)
type action
type retroknowledge

type engagement = ImpredicativeSet
let val_eng = val_enum "eng" 1


type polymorphic_arity = {
  poly_param_levels : Univ.universe option list;
  poly_level : Univ.universe;
}
let val_pol_arity =
  val_tuple ~name:"polyorphic_arity"[|val_list(val_opt val_univ);val_univ|]

type constant_type =
  | NonPolymorphicType of constr
  | PolymorphicArity of rel_context * polymorphic_arity

let val_cst_type =
  val_sum "constant_type" 0 [|[|val_constr|];[|val_rctxt;val_pol_arity|]|]


type substitution_domain =
  | MBI of mod_bound_id
  | MPI of module_path

let val_subst_dom =
  val_sum "substitution_domain" 0 [|[|val_uid|];[|val_mp|]|]

module Umap = Map.Make(struct
			 type t = substitution_domain
			 let compare = Pervasives.compare
		       end)


type delta_hint =
    Inline of constr option
  | Equiv of kernel_name
  | Prefix_equiv of module_path

type delta_key = 
    KN of kernel_name
  | MP of module_path

module Deltamap =  Map.Make(struct 
			      type t = delta_key
			      let compare = Pervasives.compare
			    end)

type delta_resolver = delta_hint Deltamap.t

let empty_delta_resolver = Deltamap.empty

type substitution = (module_path * delta_resolver) Umap.t
type 'a subst_fun = substitution -> 'a -> 'a

let val_res_dom =
  val_sum "delta_key" 0 [|[|val_kn|];[|val_mp|]|]

let val_res =
  val_map ~name:"delta_resolver"
    val_res_dom  
    (val_sum "delta_hint" 0 [|[|val_opt val_constr|];[|val_kn|];[|val_mp|]|])

let val_subst =
  val_map ~name:"substitution"
    val_subst_dom (val_tuple ~name:"substition range" [|val_mp;val_res|])


let fold_subst fb fp =
  Umap.fold
    (fun k (mp,_) acc ->
      match k with
        | MBI mbid -> fb mbid mp acc
        | MPI mp1 -> fp mp1 mp acc)

let empty_subst = Umap.empty

let add_mbid mbid mp =
  Umap.add (MBI mbid) (mp,empty_delta_resolver)
let add_mp mp1 mp2  =
  Umap.add (MPI mp1) (mp2,empty_delta_resolver)

let map_mbid mbid mp = add_mbid mbid mp empty_subst
let map_mp mp1 mp2 = add_mp mp1 mp2 empty_subst

let add_inline_delta_resolver con =
  Deltamap.add (KN(user_con con)) (Inline None)
    
let add_inline_constr_delta_resolver con cstr =
  Deltamap.add (KN(user_con con)) (Inline (Some cstr))

let add_constant_delta_resolver con =
  Deltamap.add (KN(user_con con)) (Equiv (canonical_con con))

let add_mind_delta_resolver mind =
  Deltamap.add (KN(user_mind mind)) (Equiv (canonical_mind mind))

let add_mp_delta_resolver mp1 mp2 = 
  Deltamap.add (MP mp1) (Prefix_equiv mp2)

let mp_in_delta mp = 
  Deltamap.mem (MP mp) 

let con_in_delta con resolver = 
try 
  match Deltamap.find (KN(user_con con)) resolver with
  | Inline _  | Prefix_equiv _ -> false
  | Equiv _ -> true
with
 Not_found -> false

let mind_in_delta mind resolver = 
try 
  match Deltamap.find (KN(user_mind mind)) resolver with
  | Inline _  | Prefix_equiv _ -> false
  | Equiv _ -> true
with
 Not_found -> false

let delta_of_mp resolve mp =
  try 
    match Deltamap.find (MP mp) resolve with
      | Prefix_equiv mp1 -> mp1
      | _ -> anomaly "mod_subst: bad association in delta_resolver"
  with
      Not_found -> mp

let remove_mp_delta_resolver resolver mp =
    Deltamap.remove (MP mp) resolver

exception Inline_kn

let rec find_prefix resolve mp = 
  let rec sub_mp = function
    | MPdot(mp,l) as mp_sup -> 
	(try 
	   match Deltamap.find (MP mp_sup) resolve with
	     | Prefix_equiv mp1 -> mp1
	     | _ -> anomaly 
		 "mod_subst: bad association in delta_resolver"
	 with
	     Not_found -> MPdot(sub_mp mp,l))
    | p -> 
	match Deltamap.find (MP p) resolve with
	  | Prefix_equiv mp1 -> mp1
	  | _ -> anomaly 
		 "mod_subst: bad association in delta_resolver"	
  in
    try 
      sub_mp mp
    with
	Not_found -> mp
	  
let solve_delta_kn resolve kn =
  try 
      match Deltamap.find (KN kn) resolve with
	| Equiv kn1 -> kn1
	| Inline _ -> raise Inline_kn
	| _ -> anomaly 
	    "mod_subst: bad association in delta_resolver"
  with
      Not_found | Inline_kn -> 
	let mp,dir,l = repr_kn kn in
	let new_mp = find_prefix resolve mp in
	  if mp == new_mp then 
	    kn
	  else
	    make_kn new_mp dir l
	      

let constant_of_delta resolve con =
  let kn = user_con con in
  let new_kn = solve_delta_kn resolve kn in
    if kn == new_kn then
      con
    else
      constant_of_kn_equiv kn new_kn
	
let constant_of_delta2 resolve con =
  let kn = canonical_con con in
  let kn1 = user_con con in
  let new_kn = solve_delta_kn resolve kn in
    if kn == new_kn then
      con
    else
      constant_of_kn_equiv kn1 new_kn

let mind_of_delta resolve mind =
  let kn = user_mind mind in
  let new_kn = solve_delta_kn resolve kn in
    if kn == new_kn then
      mind
    else
      mind_of_kn_equiv kn new_kn
	
let mind_of_delta2 resolve mind =
  let kn = canonical_mind mind in
  let kn1 = user_mind mind in
  let new_kn = solve_delta_kn resolve kn in
    if kn == new_kn then
      mind
    else
      mind_of_kn_equiv kn1 new_kn



let inline_of_delta resolver = 
  let extract key hint l =
    match key,hint with 
      |KN kn, Inline _ -> kn::l
      | _,_ -> l
  in
    Deltamap.fold extract resolver []

exception Not_inline
  
let constant_of_delta_with_inline resolve con =
  let kn1,kn2 = canonical_con con,user_con con in
    try
      match Deltamap.find (KN kn2) resolve with 
	| Inline None -> None
	| Inline (Some const) -> Some const
	| _ -> raise Not_inline
    with
	Not_found | Not_inline -> 
	  try match Deltamap.find (KN kn1) resolve with 
	    | Inline None -> None
	    | Inline (Some const) -> Some const
	    | _ -> raise Not_inline
	  with
	      Not_found | Not_inline -> None

let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPfile sid -> 
        let mp',resolve = Umap.find (MPI (MPfile sid)) sub in
         mp',resolve
    | MPbound bid ->
	begin
	  try
            let mp',resolve = Umap.find (MBI bid) sub in
              mp',resolve
	  with Not_found ->
	    let mp',resolve = Umap.find (MPI mp) sub in
              mp',resolve
	end
    | MPdot (mp1,l) as mp2 ->
	begin
	  try
	    let mp',resolve = Umap.find (MPI mp2) sub in
              mp',resolve
	  with Not_found ->
	    let mp1',resolve = aux mp1 in
	      MPdot (mp1',l),resolve
	end
 in
  try
    Some (aux mp)
  with Not_found -> None

let subst_mp sub mp =
 match subst_mp0 sub mp with
    None -> mp
  | Some (mp',_) -> mp'

let subst_kn_delta sub kn =
 let mp,dir,l = repr_kn kn in
  match subst_mp0 sub mp with
     Some (mp',resolve) ->
      solve_delta_kn resolve (make_kn mp' dir l)
   | None -> kn

let subst_kn sub kn =
 let mp,dir,l = repr_kn kn in
  match subst_mp0 sub mp with
     Some (mp',_) ->
      make_kn mp' dir l
   | None -> kn

exception No_subst

type sideconstantsubst =
  | User
  | Canonical

let subst_ind sub mind =
  let kn1,kn2 = user_mind mind,canonical_mind mind in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
    try 
      let side,mind',resolve =   
        match subst_mp0 sub mp1,subst_mp0 sub mp2 with
	    None,None ->raise No_subst
	  | Some (mp',resolve),None -> User,(make_mind_equiv mp' mp2 dir l), resolve
	  | None, Some(mp',resolve)-> Canonical,(make_mind_equiv mp1 mp' dir l), resolve
	  | Some(mp1',resolve1),Some(mp2',resolve2)->Canonical,
	      (make_mind_equiv mp1' mp2' dir l), resolve2 
      in
	match side with
	  |User ->
	     let mind = mind_of_delta resolve mind' in
	       mind
	  |Canonical ->
	     let mind = mind_of_delta2 resolve mind' in
	       mind
    with 
	No_subst -> mind

let subst_mind0 sub mind =
  let kn1,kn2 = user_mind mind,canonical_mind mind in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
    try 
      let side,mind',resolve =   
        match subst_mp0 sub mp1,subst_mp0 sub mp2 with
	    None,None ->raise No_subst
	  | Some (mp',resolve),None -> User,(make_mind_equiv mp' mp2 dir l), resolve
	  | None, Some(mp',resolve)-> Canonical,(make_mind_equiv mp1 mp' dir l), resolve
	  | Some(mp1',resolve1),Some(mp2',resolve2)->Canonical,
	      (make_mind_equiv mp1' mp2' dir l), resolve2
      in
	match side with
	  |User ->
	     let mind = mind_of_delta resolve mind' in
	       Some mind
	  |Canonical ->
	     let mind = mind_of_delta2 resolve mind' in
	       Some mind
    with 
	No_subst -> Some mind

let subst_con sub con =
  let kn1,kn2 = user_con con,canonical_con con in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
    try 
      let side,con',resolve =   
        match subst_mp0 sub mp1,subst_mp0 sub mp2 with
	    None,None ->raise No_subst
	  | Some (mp',resolve),None -> User,(make_con_equiv mp' mp2 dir l), resolve
	  | None, Some(mp',resolve)-> Canonical,(make_con_equiv mp1 mp' dir l), resolve
	  | Some(mp1',resolve1),Some(mp2',resolve2)->Canonical,
	      (make_con_equiv mp1' mp2' dir l), resolve2 
      in
	match constant_of_delta_with_inline resolve con' with
            None -> begin
	      match side with
	      |User ->
	      let con = constant_of_delta resolve con' in
		con,Const con
	      |Canonical ->
		  let con = constant_of_delta2 resolve con' in
		con,Const con
	    end
	  | Some t -> con',t
    with No_subst -> con , Const con 
 

let subst_con0 sub con =
  let kn1,kn2 = user_con con,canonical_con con in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
    try  
      let side,con',resolve =   
	match subst_mp0 sub mp1,subst_mp0 sub mp2 with
	    None,None ->raise No_subst
	  | Some (mp',resolve),None -> User,(make_con_equiv mp' mp2 dir l), resolve
	  | None, Some(mp',resolve)-> Canonical,(make_con_equiv mp1 mp' dir l), resolve
	  | Some(mp1',resolve1),Some(mp2',resolve2)->Canonical,
	      (make_con_equiv mp1' mp2' dir l), resolve2 
      in
	match constant_of_delta_with_inline resolve con' with
	    None ->begin
	      match side with
	      |User ->
	      let con = constant_of_delta resolve con' in
		Some (Const con)
	      |Canonical ->
		  let con = constant_of_delta2 resolve con' in
		Some (Const con)
	    end
	  | t ->  t
    with No_subst -> Some (Const con)


let rec map_kn f f' c =
  let func = map_kn f f' in
    match c with
      | Const kn ->
	  (match f' kn with
	       None -> c
	     | Some const ->const)
      | Ind (kn,i) ->
         (match f kn with
             None -> c
           | Some kn' ->
	      Ind (kn',i))
      | Construct ((kn,i),j) ->
         (match f kn with
             None -> c
           | Some kn' ->
	       Construct ((kn',i),j))
      | Case (ci,p,ct,l) ->
	  let ci_ind =
            let (kn,i) = ci.ci_ind in
              (match f kn with None -> ci.ci_ind | Some kn' -> kn',i ) in
	  let p' = func p in
	  let ct' = func ct in
	  let l' = array_smartmap func l in
	    if (ci.ci_ind==ci_ind && p'==p
		&& l'==l && ct'==ct)then c
	    else
	      Case ({ci with ci_ind = ci_ind},
		     p',ct', l')
      | Cast (ct,k,t) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else Cast (ct', k, t')
      | Prod (na,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else Prod (na, t', ct')
      | Lambda (na,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else Lambda (na, t', ct')
      | LetIn (na,b,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	  let b'= func b in
	    if (t'==t && ct'==ct && b==b') then c
	    else LetIn (na, b', t', ct')
      | App (ct,l) ->
	  let ct' = func ct in
	  let l' = array_smartmap func l in
	    if (ct'== ct && l'==l) then c
	    else App (ct',l')
      | Evar (e,l) ->
	  let l' = array_smartmap func l in
	    if (l'==l) then c
	    else Evar (e,l')
      | Fix (ln,(lna,tl,bl)) ->
	  let tl' = array_smartmap func tl in
	  let bl' = array_smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else Fix (ln,(lna,tl',bl'))
      | CoFix(ln,(lna,tl,bl)) ->
	  let tl' = array_smartmap func tl in
	  let bl' = array_smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else CoFix (ln,(lna,tl',bl'))
      | _ -> c

let subst_mps sub =
  map_kn (subst_mind0 sub) (subst_con0 sub)


type 'a lazy_subst =
  | LSval of 'a
  | LSlazy of substitution list * 'a

type 'a substituted = 'a lazy_subst ref

let val_substituted val_a =
  val_ref
    (val_sum "constr_substituted" 0
      [|[|val_a|];[|val_list val_subst;val_a|]|])

let from_val a = ref (LSval a)
 
let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when mp = mpfrom -> mpto
    | MPdot (mp1,l) ->
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1==mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let rec mp_in_mp mp mp1 =
  match mp1 with
    | _ when mp1 = mp -> true
    | MPdot (mp2,l) -> mp_in_mp mp mp2
    | _ -> false
	
let mp_in_key mp key = 
  match key with
    | MP mp1 -> 
	mp_in_mp mp mp1
    | KN kn -> 
	let mp1,dir,l = repr_kn kn in
	  mp_in_mp mp mp1
  
let subset_prefixed_by mp resolver =
  let prefixmp key hint resolv =
    if mp_in_key mp key then
      Deltamap.add key hint resolv
    else 
      resolv
  in
    Deltamap.fold prefixmp resolver empty_delta_resolver

let subst_dom_delta_resolver subst resolver =
  let apply_subst key hint resolver =
    match key with
	(MP mp) ->
	  Deltamap.add (MP (subst_mp subst mp)) hint resolver
      | (KN kn) ->
	  Deltamap.add (KN (subst_kn subst kn)) hint resolver
  in
    Deltamap.fold apply_subst resolver empty_delta_resolver

let subst_mp_delta sub mp key=
 match subst_mp0 sub mp with
    None -> empty_delta_resolver,mp
  | Some (mp',resolve) -> 
      let mp1 = find_prefix resolve mp' in
      let resolve1 = subset_prefixed_by mp1 resolve in
	match key with
	    MP mpk ->
	      (subst_dom_delta_resolver 
		 (map_mp mp1 mpk) resolve1),mp1
	  | _ -> anomaly "Mod_subst: Bad association in resolver" 

let subst_codom_delta_resolver subst resolver =
  let apply_subst key hint resolver =
    match hint with
	Prefix_equiv mp ->
	  let derived_resolve,mpnew = subst_mp_delta subst mp key in
	    Deltamap.fold Deltamap.add derived_resolve
	      (Deltamap.add key (Prefix_equiv mpnew) resolver)
      | (Equiv kn) ->
	  Deltamap.add key (Equiv (subst_kn_delta subst kn)) resolver
      | Inline None ->
	  Deltamap.add key hint resolver
      | Inline (Some t) ->
	  Deltamap.add key (Inline (Some (subst_mps subst t))) resolver
  in
    Deltamap.fold apply_subst resolver empty_delta_resolver

let subst_dom_codom_delta_resolver subst resolver =
  subst_dom_delta_resolver subst
    (subst_codom_delta_resolver subst resolver)
    
let update_delta_resolver resolver1 resolver2 =
 let apply_res key hint res = 
      try
	match hint with
	    Prefix_equiv mp ->
	      let new_hint =
		Prefix_equiv (find_prefix resolver2 mp)
	      in Deltamap.add key new_hint res
	  | Equiv kn ->
	      let new_hint =
		Equiv (solve_delta_kn resolver2 kn)
	      in Deltamap.add key new_hint res
	  | _ -> Deltamap.add key hint res
      with Not_found ->
	Deltamap.add key hint res
    in
      Deltamap.fold apply_res resolver1 empty_delta_resolver

let add_delta_resolver resolver1 resolver2 =
  if resolver1 == resolver2 then
    resolver2
  else
    Deltamap.fold Deltamap.add (update_delta_resolver resolver1 resolver2)
      resolver2

let substition_prefixed_by k mp subst =
  let prefixmp key (mp_to,reso) sub =
    match key with 
      | MPI mpk ->
	  if mp_in_mp mp mpk && mp <> mpk then
	    let new_key = replace_mp_in_mp mp k mpk in
	      Umap.add (MPI new_key) (mp_to,reso) sub
	  else 
	    sub
      |  _ -> sub
  in
    Umap.fold prefixmp subst empty_subst

let join (subst1 : substitution) (subst2 : substitution) =
  let apply_subst key (mp,resolve) res =
    let mp',resolve' =
      match subst_mp0 subst2 mp with
	  None -> mp, None
	| Some (mp',resolve') ->  mp'
	    ,Some resolve' in
    let resolve'' : delta_resolver =
      match resolve' with
          Some res -> 
	    add_delta_resolver 
	      (subst_dom_codom_delta_resolver subst2 resolve) res
	| None -> 
	    subst_codom_delta_resolver subst2 resolve
    in
    let k = match key with MBI mp -> MPbound mp | MPI mp -> mp in
    let prefixed_subst = substition_prefixed_by k mp subst2 in
      Umap.fold Umap.add prefixed_subst 
	(Umap.add key (mp',resolve'') res) in
  let subst = Umap.fold apply_subst subst1 empty_subst in
    (Umap.fold Umap.add subst2 subst) 

let force fsubst r =
  match !r with
  | LSval a -> a
  | LSlazy(s,a) ->
      let subst = List.fold_left join empty_subst (List.rev s) in
      let a' = fsubst subst a in
      r := LSval a';
      a'

let subst_substituted s r =
  match !r with
    | LSval a -> ref (LSlazy([s],a))
    | LSlazy(s',a) ->
	  ref (LSlazy(s::s',a))

let force_constr = force subst_mps

type constr_substituted = constr substituted

let val_cstr_subst = val_substituted val_constr

let subst_constr_subst = subst_substituted

type constant_body = {
    const_hyps : section_context; (* New: younger hyp at top *)
    const_body : constr_substituted option;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
   (* const_type_code : Cemitcodes.to_patch; *)
    const_constraints : Univ.constraints;
    const_opaque : bool;
    const_inline : bool}

let val_cb = val_tuple ~name:"constant_body"
  [|val_nctxt;
    val_opt val_cstr_subst;
    val_cst_type;
    no_val;
    val_cstrs;
    val_bool;
    val_bool |]


let subst_rel_declaration sub (id,copt,t as x) =
  let copt' = Option.smartmap (subst_mps sub) copt in
  let t' = subst_mps sub t in
  if copt == copt' & t == t' then x else (id,copt',t')

let subst_rel_context sub = list_smartmap (subst_rel_declaration sub)

type recarg =
  | Norec
  | Mrec of inductive
  | Imbr of inductive
let val_recarg = val_sum "recarg" 1 (* Norec *)
  [|[|val_ind|] (* Mrec *);[|val_ind|] (* Imbr *)|]

let subst_recarg sub r = match r with
  | Norec  -> r
  | (Mrec(kn,i)|Imbr (kn,i)) -> let kn' = subst_ind sub kn in
      if kn==kn' then r else Imbr (kn',i)

type wf_paths = recarg Rtree.t
let val_wfp = val_rec_sum "wf_paths" 0
  (fun val_wfp ->
    [|[|val_int;val_int|]; (* Rtree.Param *)
      [|val_recarg;val_array val_wfp|]; (* Rtree.Node *)
      [|val_int;val_array val_wfp|] (* Rtree.Rec *)
    |])

let mk_norec = Rtree.mk_node Norec [||]

let mk_paths r recargs =
  Rtree.mk_node r
    (Array.map (fun l -> Rtree.mk_node Norec (Array.of_list l)) recargs)

let dest_recarg p = fst (Rtree.dest_node p)

let dest_subterms p =
  let (_,cstrs) = Rtree.dest_node p in
  Array.map (fun t -> Array.to_list (snd (Rtree.dest_node t))) cstrs

let subst_wf_paths sub p = Rtree.smartmap (subst_recarg sub) p

(**********************************************************************)
(* Representation of mutual inductive types in the kernel             *)
(*
   Inductive I1 (params) : U1 := c11 : T11 | ... | c1p1 : T1p1
   ...
   with      In (params) : Un := cn1 : Tn1 | ... | cnpn : Tnpn
*)

type monomorphic_inductive_arity = {
  mind_user_arity : constr;
  mind_sort : sorts;
}
let val_mono_ind_arity =
  val_tuple ~name:"monomorphic_inductive_arity"[|val_constr;val_sort|]

type inductive_arity =
| Monomorphic of monomorphic_inductive_arity
| Polymorphic of polymorphic_arity
let val_ind_arity = val_sum "inductive_arity" 0
  [|[|val_mono_ind_arity|];[|val_pol_arity|]|]

type one_inductive_body = {

(* Primitive datas *)

 (* Name of the type: [Ii] *)
    mind_typename : identifier;

 (* Arity context of [Ii] with parameters: [forall params, Ui] *)
    mind_arity_ctxt : rel_context;

 (* Arity sort, original user arity, and allowed elim sorts, if monomorphic *)
    mind_arity : inductive_arity;

 (* Names of the constructors: [cij] *)
    mind_consnames : identifier array;

 (* Types of the constructors with parameters: [forall params, Tij],
    where the Ik are replaced by de Bruijn index in the context
    I1:forall params, U1 ..  In:forall params, Un *)
    mind_user_lc : constr array;

(* Derived datas *)

 (* Number of expected real arguments of the type (no let, no params) *)
    mind_nrealargs : int;

 (* Length of realargs context (with let, no params) *)
    mind_nrealargs_ctxt : int;

 (* List of allowed elimination sorts *)
    mind_kelim : sorts_family list;

 (* Head normalized constructor types so that their conclusion is atomic *)
    mind_nf_lc : constr array;

 (* Length of the signature of the constructors (with let, w/o params) *)
    mind_consnrealdecls : int array;

 (* Signature of recursive arguments in the constructors *)
    mind_recargs : wf_paths;

(* Datas for bytecode compilation *)

 (* number of constant constructor *)
    mind_nb_constant : int;

 (* number of no constant constructor *)
    mind_nb_args : int;

    mind_reloc_tbl :  reloc_table;
  }

let val_one_ind = val_tuple ~name:"one_inductive_body"
  [|val_id;val_rctxt;val_ind_arity;val_array val_id;val_array val_constr;
    val_int;val_int;val_list val_sortfam;val_array val_constr;val_array val_int;
    val_wfp;val_int;val_int;no_val|]


type mutual_inductive_body = {

  (* The component of the mutual inductive block *)
    mind_packets : one_inductive_body array;

  (* Whether the inductive type has been declared as a record *)
    mind_record : bool;

  (* Whether the type is inductive or coinductive *)
    mind_finite : bool;

  (* Number of types in the block *)
    mind_ntypes : int;

  (* Section hypotheses on which the block depends *)
    mind_hyps : section_context;

  (* Number of expected parameters *)
    mind_nparams : int;

  (* Number of recursively uniform (i.e. ordinary) parameters *)
    mind_nparams_rec : int;

  (* The context of parameters (includes let-in declaration) *)
    mind_params_ctxt : rel_context;

  (* Universes constraints enforced by the inductive declaration *)
    mind_constraints : Univ.constraints;

  }
let val_ind_pack = val_tuple ~name:"mutual_inductive_body"
  [|val_array val_one_ind;val_bool;val_bool;val_int;val_nctxt;
    val_int; val_int; val_rctxt;val_cstrs|]


let subst_arity sub = function
| NonPolymorphicType s -> NonPolymorphicType (subst_mps sub s)
| PolymorphicArity (ctx,s) -> PolymorphicArity (subst_rel_context sub ctx,s)

(* TODO: should be changed to non-coping after Term.subst_mps *)
let subst_const_body sub cb = {
    const_hyps = (assert (cb.const_hyps=[]); []);
    const_body = Option.map (subst_constr_subst sub) cb.const_body;
    const_type = subst_arity sub cb.const_type;
    const_body_code = (*Cemitcodes.subst_to_patch_subst sub*) cb.const_body_code;
    (*const_type_code = Cemitcodes.subst_to_patch sub cb.const_type_code;*)
    const_constraints = cb.const_constraints;
    const_opaque = cb.const_opaque;
    const_inline = cb.const_inline}

let subst_arity sub = function
| Monomorphic s ->
    Monomorphic {
      mind_user_arity = subst_mps sub s.mind_user_arity;
      mind_sort = s.mind_sort;
    }
| Polymorphic s as x -> x

let subst_mind_packet sub mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_typename = mbp.mind_typename;
   mind_nf_lc = array_smartmap (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_arity sub mbp.mind_arity;
    mind_user_lc = array_smartmap (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealargs_ctxt = mbp.mind_nrealargs_ctxt;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }


let subst_mind sub mib =
  { mind_record = mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (assert (mib.mind_hyps=[]); []) ;
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt =
      map_rel_context (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = array_smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_constraints = mib.mind_constraints  }

(* Modules *)

(* Whenever you change these types, please do update the validation
   functions below *)
type structure_field_body =
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBmodtype of module_type_body

and structure_body = (label * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of mod_bound_id * module_type_body * struct_expr_body
  | SEBapply of struct_expr_body * struct_expr_body * Univ.constraints
  | SEBstruct of structure_body
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of identifier list * module_path
  | With_definition_body of  identifier list * constant_body

and module_body =
    { mod_mp : module_path;
      mod_expr : struct_expr_body option; 
      mod_type : struct_expr_body;
      mod_type_alg : struct_expr_body option;
      mod_constraints : Univ.constraints;
      mod_delta : delta_resolver;
      mod_retroknowledge : action list}

and module_type_body =
    { typ_mp : module_path;
      typ_expr : struct_expr_body;
      typ_expr_alg : struct_expr_body option ;
      typ_constraints : Univ.constraints;
      typ_delta :delta_resolver}

(* the validation functions: *)
let rec val_sfb o = val_sum "struct_field_body" 0
  [|[|val_cb|];       (* SFBconst *)
    [|val_ind_pack|]; (* SFBmind *)
    [|val_module|];   (* SFBmodule *)
    [|val_modtype|]   (* SFBmodtype *)
  |] o
and val_sb o = val_list (val_tuple ~name:"label*sfb"[|val_id;val_sfb|]) o
and val_seb o = val_sum "struct_expr_body" 0
  [|[|val_mp|];                      (* SEBident *)
    [|val_uid;val_modtype;val_seb|]; (* SEBfunctor *)
    [|val_seb;val_seb;val_cstrs|];   (* SEBapply *)
    [|val_sb|];              (* SEBstruct *)
    [|val_seb;val_with|]             (* SEBwith *)
  |] o
and val_with o = val_sum "with_declaration_body" 0
  [|[|val_list val_id;val_mp|];
    [|val_list val_id;val_cb|]|] o
and val_module o = val_tuple ~name:"module_body"
  [|val_mp;val_opt val_seb;val_seb;
    val_opt val_seb;val_cstrs;val_res;no_val|] o
and val_modtype o = val_tuple ~name:"module_type_body"
  [|val_mp;val_seb;val_opt val_seb;val_cstrs;val_res|] o


let rec subst_with_body sub = function
  | With_module_body(id,mp) ->
      With_module_body(id,subst_mp sub mp)
  | With_definition_body(id,cb) ->
      With_definition_body( id,subst_const_body sub cb)

and subst_modtype sub mtb=
  let typ_expr' = subst_struct_expr sub mtb.typ_expr in
  let typ_alg' = 
    Option.smartmap 
      (subst_struct_expr sub) mtb.typ_expr_alg in
  let mp = subst_mp sub mtb.typ_mp
  in
    if typ_expr'==mtb.typ_expr && 
      typ_alg'==mtb.typ_expr_alg && mp==mtb.typ_mp then
	mtb
    else
      {mtb with 
	 typ_mp = mp;
	 typ_expr = typ_expr';
	 typ_expr_alg = typ_alg'}

and subst_structure sub sign = 
  let subst_body = function
      SFBconst cb -> 
	SFBconst (subst_const_body sub cb)
    | SFBmind mib -> 
	SFBmind (subst_mind sub mib)
    | SFBmodule mb -> 
	SFBmodule (subst_module sub  mb)
    | SFBmodtype mtb -> 
	SFBmodtype (subst_modtype sub mtb)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign


and subst_module sub mb =
  let mtb' = subst_struct_expr sub mb.mod_type in
  let typ_alg' = Option.smartmap 
    (subst_struct_expr sub ) mb.mod_type_alg in
  let me' = Option.smartmap 
    (subst_struct_expr sub) mb.mod_expr in
  let mp = subst_mp sub mb.mod_mp in
     if mtb'==mb.mod_type && mb.mod_expr == me' 
       && mp == mb.mod_mp
    then mb else
      { mb with
	  mod_mp = mp;
	  mod_expr = me';
	  mod_type_alg = typ_alg';
	  mod_type=mtb'}

and subst_struct_expr sub = function
    | SEBident mp -> SEBident (subst_mp sub mp)
    | SEBfunctor (mbid, mtb, meb') -> 
	SEBfunctor(mbid,subst_modtype sub mtb
		     ,subst_struct_expr sub meb')
    | SEBstruct (str)->
	SEBstruct( subst_structure sub  str)
    | SEBapply (meb1,meb2,cst)->
	SEBapply(subst_struct_expr sub meb1,
		 subst_struct_expr sub meb2,
		 cst)
    | SEBwith (meb,wdb)-> 
	SEBwith(subst_struct_expr sub meb,
		subst_with_body sub wdb)


