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

type substitution_domain = 
  | MBI of mod_bound_id
  | MPI of module_path

let string_of_subst_domain = function
 | MBI mbid -> debug_string_of_mbid mbid
 | MPI mp -> string_of_mp mp

module Umap = Map.Make(struct
			 type t = substitution_domain
			 let compare = Pervasives.compare
		       end)

type substitution = (module_path * delta_resolver) Umap.t
    
let empty_subst = Umap.empty


let string_of_subst_domain = function
  | MBI mbid -> debug_string_of_mbid mbid
  | MPI mp -> string_of_mp mp
      
let add_mbid mbid mp resolve =
  Umap.add (MBI mbid) (mp,resolve)
let add_mp mp1 mp2 resolve =
  Umap.add (MPI mp1) (mp2,resolve)


let map_mbid mbid mp resolve = add_mbid mbid mp resolve empty_subst
let map_mp mp1 mp2 resolve = add_mp mp1 mp2 resolve empty_subst

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
	
let delta_of_kn resolve kn =
  try 
    match Deltamap.find (KN kn) resolve with
      | Equiv kn1 -> kn1
      | Inline _ -> kn
      | _ -> anomaly 
	  "mod_subst: bad association in delta_resolver"
  with
      Not_found -> kn

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

let string_of_key = function
      | KN kn -> string_of_kn kn
      | MP mp -> string_of_mp mp

let string_of_hint = function
      | Inline _ -> "inline"
      | Equiv kn -> string_of_kn kn
      | Prefix_equiv mp -> string_of_mp mp

let debug_string_of_delta resolve =
  let to_string key hint s = 
    s^", "^(string_of_key key)^"=>"^(string_of_hint hint)
  in 
    Deltamap.fold to_string resolve ""  
      
let list_contents sub = 
  let one_pair uid (mp,reso) l =
    (string_of_subst_domain uid, string_of_mp mp,debug_string_of_delta reso)::l
  in
    Umap.fold one_pair sub []
      
let debug_string_of_subst sub =
  let l = List.map (fun (s1,s2,s3) -> s1^"|->"^s2^"["^s3^"]")
    (list_contents sub) in
    "{" ^ String.concat "; " l ^ "}"
      
let debug_pr_delta resolve = 
  str (debug_string_of_delta resolve)

let debug_pr_subst sub =
  let l = list_contents sub in
  let f (s1,s2,s3) = hov 2 (str s1 ++ spc () ++ str "|-> " ++ str s2 ++
			      spc () ++ str "[" ++ str s3 ++ str "]") 
  in
    str "{" ++ hov 2 (prlist_with_sep pr_coma f l) ++ str "}"
      
      
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
      (make_kn mp' dir l)
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
		con,mkConst con
	      |Canonical ->
		  let con = constant_of_delta2 resolve con' in
		con,mkConst con
	    end
	  | Some t -> con',t
    with No_subst -> con , mkConst con 
 

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
		Some (mkConst con)
	      |Canonical ->
		  let con = constant_of_delta2 resolve con' in
		Some (mkConst con)
	    end
	  | t ->  t
    with No_subst -> Some (mkConst con) 
		
(* Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
let subst_evaluable_reference subst = function
  | EvalVarRef id -> EvalVarRef id
  | EvalConstRef kn -> EvalConstRef (fst (subst_con subst kn))



let rec map_kn f f' c =
  let func = map_kn f f' in
    match kind_of_term c with
      | Const kn ->
	  (match f' kn with
	       None -> c
	     | Some const ->const)
      | Ind (kn,i) ->
         (match f kn with
             None -> c
           | Some kn' ->
	      mkInd (kn',i))
      | Construct ((kn,i),j) ->
         (match f kn with
             None -> c
           | Some kn' ->
	       mkConstruct ((kn',i),j))
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
	      mkCase ({ci with ci_ind = ci_ind},
		      p',ct', l')
      | Cast (ct,k,t) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else mkCast (ct', k, t')
      | Prod (na,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else mkProd (na, t', ct')
      | Lambda (na,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else mkLambda (na, t', ct')
      | LetIn (na,b,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	  let b'= func b in
	    if (t'==t && ct'==ct && b==b') then c
	    else mkLetIn (na, b', t', ct')
      | App (ct,l) ->
	  let ct' = func ct in
	  let l' = array_smartmap func l in
	    if (ct'== ct && l'==l) then c
	    else mkApp (ct',l')
      | Evar (e,l) ->
	  let l' = array_smartmap func l in
	    if (l'==l) then c
	    else mkEvar (e,l')
      | Fix (ln,(lna,tl,bl)) ->
	  let tl' = array_smartmap func tl in
	  let bl' = array_smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else mkFix (ln,(lna,tl',bl'))
      | CoFix(ln,(lna,tl,bl)) ->
	  let tl' = array_smartmap func tl in
	  let bl' = array_smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else mkCoFix (ln,(lna,tl',bl'))
      | _ -> c

let subst_mps sub =
  map_kn (subst_mind0 sub) (subst_con0 sub)

let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when mp = mpfrom -> mpto
    | MPdot (mp1,l) ->
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1==mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let replace_mp_in_kn mpfrom mpto kn =
 let mp,dir,l = repr_kn kn in
  let mp'' = replace_mp_in_mp mpfrom mpto mp in
    if mp==mp'' then kn
    else make_kn mp'' dir l

let mp_in_key mp key = 
  let rec mp_rec mp1 = 
    match mp1 with
      | _ when mp1 = mp -> true
      | MPdot (mp2,l) -> mp_rec mp2
      | _ -> false
  in 
    match key with
    | MP mp1 -> 
	mp_rec mp1
    | KN kn -> 
	let mp1,dir,l = repr_kn kn in
	  mp_rec mp1
   
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
		 (map_mp mp1 mpk empty_delta_resolver) resolve1),mp1
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
  let apply_subst key hint resolver =
    match key,hint with
	(MP mp1),Prefix_equiv mp ->
	  let key = MP (subst_mp subst mp1) in
	  let derived_resolve,mpnew = subst_mp_delta subst mp key in
	    Deltamap.fold Deltamap.add derived_resolve
	      (Deltamap.add key (Prefix_equiv mpnew) resolver)
      | (KN kn1),(Equiv kn) ->
	  let key = KN (subst_kn subst kn1) in
	  Deltamap.add key (Equiv (subst_kn_delta subst kn)) resolver
      | (KN kn),Inline None ->
	  let key = KN (subst_kn subst kn) in
	  Deltamap.add key hint resolver
      | (KN kn),Inline (Some t) ->
	  let key = KN (subst_kn subst kn) in
	  Deltamap.add key (Inline (Some (subst_mps subst t))) resolver
      | _,_ -> anomaly "Mod_subst: Bad association in resolver" 
  in
    Deltamap.fold apply_subst resolver empty_delta_resolver

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
      with not_found -> 
	Deltamap.add key hint res
    in
      Deltamap.fold apply_res resolver1 empty_delta_resolver

let add_delta_resolver resolver1 resolver2 =
  if resolver1 == resolver2 then
    resolver2
  else if resolver2 = empty_delta_resolver then
    resolver1
  else
    Deltamap.fold Deltamap.add (update_delta_resolver resolver1 resolver2)
      resolver2

let join (subst1 : substitution) (subst2 : substitution) =
  let apply_subst (sub : substitution) key (mp,resolve) =
    let mp',resolve' =
      match subst_mp0 sub mp with
	  None -> mp, None
	| Some (mp',resolve') ->  mp'
	    ,Some resolve' in
    let resolve'' : delta_resolver =
      match resolve' with
          Some res -> 
	    add_delta_resolver 
	      (subst_dom_codom_delta_resolver sub resolve)
	      res
	| None -> 
	    subst_codom_delta_resolver sub resolve
    in
      mp',resolve'' in
  let subst = Umap.mapi (apply_subst subst2) subst1 in
    (Umap.fold Umap.add subst2 subst)   



let rec occur_in_path uid path =
 match uid,path with
  | MBI bid,MPbound bid' -> bid = bid'
  | _,MPdot (mp1,_) -> occur_in_path uid mp1
  | _ -> false

let occur_uid uid sub =
  let check_one uid' (mp,_) =
    if uid = uid' || occur_in_path uid mp then raise Exit
  in
    try
      Umap.iter check_one sub;
      false
    with Exit -> true


let occur_mbid uid = occur_uid (MBI uid)

type 'a lazy_subst =
  | LSval of 'a
  | LSlazy of substitution * 'a

type 'a substituted = 'a lazy_subst ref

let from_val a = ref (LSval a)

let force fsubst r =
  match !r with
  | LSval a -> a
  | LSlazy(s,a) ->
      let a' = fsubst s a in
      r := LSval a';
      a'

let subst_substituted s r =
  match !r with
    | LSval a -> ref (LSlazy(s,a))
    | LSlazy(s',a) ->
	let s'' = join s' s in
	  ref (LSlazy(s'',a))

