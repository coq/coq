open Util
open Names
open Cic
open Term

(** Substitutions, code imported from kernel/mod_subst *)

module Deltamap = struct
  type t = delta_resolver
  let empty = MPmap.empty, KNmap.empty
  let is_empty (mm, km) = MPmap.is_empty mm && KNmap.is_empty km
  let add_kn kn hint (mm,km) = (mm,KNmap.add kn hint km)
  let add_mp mp mp' (mm,km) = (MPmap.add mp mp' mm, km)
  let remove_mp mp (mm,km) = (MPmap.remove mp mm, km)
  let find_mp mp map = MPmap.find mp (fst map)
  let find_kn kn map = KNmap.find kn (snd map)
  let mem_mp mp map = MPmap.mem mp (fst map)
  let mem_kn kn map = KNmap.mem kn (snd map)
  let fold_kn f map i = KNmap.fold f (snd map) i
  let fold fmp fkn (mm,km) i =
    MPmap.fold fmp mm (KNmap.fold fkn km i)
  let join map1 map2 = fold add_mp add_kn map1 map2
end

let empty_delta_resolver = Deltamap.empty

module Umap = struct
  type 'a t = 'a umap_t
  let empty = MPmap.empty, MBImap.empty
  let is_empty (m1,m2) = MPmap.is_empty m1 && MBImap.is_empty m2
  let add_mbi mbi x (m1,m2) = (m1,MBImap.add mbi x m2)
  let add_mp mp x (m1,m2) = (MPmap.add mp x m1, m2)
  let find_mp mp map = MPmap.find mp (fst map)
  let find_mbi mbi map = MBImap.find mbi (snd map)
  let mem_mp mp map = MPmap.mem mp (fst map)
  let mem_mbi mbi map = MBImap.mem mbi (snd map)
  let iter_mbi f map = MBImap.iter f (snd map)
  let fold fmp fmbi (m1,m2) i =
    MPmap.fold fmp m1 (MBImap.fold fmbi m2 i)
  let join map1 map2 = fold add_mp add_mbi map1 map2
end

type 'a subst_fun = substitution -> 'a -> 'a

let empty_subst = Umap.empty

let is_empty_subst = Umap.is_empty

let add_mbid mbid mp = Umap.add_mbi mbid (mp,empty_delta_resolver)
let add_mp mp1 mp2 = Umap.add_mp mp1 (mp2,empty_delta_resolver)

let map_mbid mbid mp = add_mbid mbid mp empty_subst
let map_mp mp1 mp2 = add_mp mp1 mp2 empty_subst

let mp_in_delta mp =
  Deltamap.mem_mp mp

let find_prefix resolve mp =
  let rec sub_mp = function
    | MPdot(mp,l) as mp_sup ->
	(try Deltamap.find_mp mp_sup resolve
	 with Not_found -> MPdot(sub_mp mp,l))
    | p -> Deltamap.find_mp p resolve
  in
  try sub_mp mp with Not_found -> mp

(** Nota: the following function is slightly different in mod_subst
    PL: Is it on purpose ? *)

let solve_delta_kn resolve kn =
  try
    match Deltamap.find_kn kn resolve with
      | Equiv kn1 -> kn1
      | Inline _ -> raise Not_found
  with Not_found ->
    let mp,dir,l = repr_kn kn in
    let new_mp = find_prefix resolve mp in
    if mp == new_mp then
      kn
    else
      make_kn new_mp dir l

let gen_of_delta resolve x kn fix_can =
  let new_kn = solve_delta_kn resolve kn in
  if kn == new_kn then x else fix_can new_kn

let constant_of_delta resolve con =
  let kn = user_con con in
  gen_of_delta resolve con kn (constant_of_kn_equiv kn)

let constant_of_delta2 resolve con =
  let kn, kn' = canonical_con con, user_con con in
  gen_of_delta resolve con kn (constant_of_kn_equiv kn')

let mind_of_delta resolve mind =
  let kn = user_mind mind in
  gen_of_delta resolve mind kn (mind_of_kn_equiv kn)

let mind_of_delta2 resolve mind =
  let kn, kn' = canonical_mind mind, user_mind mind in
  gen_of_delta resolve mind kn (mind_of_kn_equiv kn')

let find_inline_of_delta kn resolve =
  match Deltamap.find_kn kn resolve with
    | Inline (_,o) -> o
    | _ -> raise Not_found

let constant_of_delta_with_inline resolve con =
  let kn1,kn2 = canonical_con con,user_con con in
  try find_inline_of_delta kn2 resolve
  with Not_found ->
    try find_inline_of_delta kn1 resolve
    with Not_found -> None

let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPfile sid -> Umap.find_mp mp sub
    | MPbound bid ->
	begin
	  try Umap.find_mbi bid sub
	  with Not_found -> Umap.find_mp mp sub
	end
    | MPdot (mp1,l) as mp2 ->
	begin
	  try Umap.find_mp mp2 sub
	  with Not_found ->
	    let mp1',resolve = aux mp1 in
	    MPdot (mp1',l),resolve
	end
 in
 try Some (aux mp) with Not_found -> None

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


let gen_subst_mp f sub mp1 mp2 =
  match subst_mp0 sub mp1, subst_mp0 sub mp2 with
    | None, None -> raise No_subst
    | Some (mp',resolve), None -> User, (f mp' mp2), resolve
    | None, Some (mp',resolve) -> Canonical, (f mp1 mp'), resolve
    | Some (mp1',_), Some (mp2',resolve2) -> Canonical, (f mp1' mp2'), resolve2

let make_mind_equiv mpu mpc dir l =
  let knu = make_kn mpu dir l in
  if mpu == mpc then mind_of_kn knu
  else mind_of_kn_equiv knu (make_kn mpc dir l)

let subst_ind sub mind =
  let kn1,kn2 = user_mind mind, canonical_mind mind in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
  let rebuild_mind mp1 mp2 = make_mind_equiv mp1 mp2 dir l in
  try
    let side,mind',resolve = gen_subst_mp rebuild_mind sub mp1 mp2 in
    match side with
      | User -> mind_of_delta resolve mind'
      | Canonical -> mind_of_delta2 resolve mind'
  with No_subst -> mind

let make_con_equiv mpu mpc dir l =
  let knu = make_kn mpu dir l in
  if mpu == mpc then constant_of_kn knu
  else constant_of_kn_equiv knu (make_kn mpc dir l)

let subst_con0 sub con =
  let kn1,kn2 = user_con con,canonical_con con in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
  let rebuild_con mp1 mp2 = make_con_equiv mp1 mp2 dir l in
  let dup con = con, Const con in
  let side,con',resolve = gen_subst_mp rebuild_con sub mp1 mp2 in
  match constant_of_delta_with_inline resolve con' with
    | Some t -> con', t
    | None ->
      let con'' = match side with
	| User -> constant_of_delta resolve con'
	| Canonical -> constant_of_delta2 resolve con'
      in
      if con'' == con then raise No_subst else dup con''

let rec map_kn f f' c =
  let func = map_kn f f' in
    match c with
      | Const kn -> (try snd (f' kn) with No_subst -> c)
      | Ind (kn,i) ->
	  let kn' = f kn in
	  if kn'==kn then c else Ind (kn',i)
      | Construct ((kn,i),j) ->
	  let kn' = f kn in
	  if kn'==kn then c else Construct ((kn',i),j)
      | Case (ci,p,ct,l) ->
	  let ci_ind =
            let (kn,i) = ci.ci_ind in
	    let kn' = f kn in
	    if kn'==kn then ci.ci_ind else kn',i
	  in
	  let p' = func p in
	  let ct' = func ct in
	  let l' = Array.smartmap func l in
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
	  let l' = Array.smartmap func l in
	    if (ct'== ct && l'==l) then c
	    else App (ct',l')
      | Evar (e,l) ->
	  let l' = Array.smartmap func l in
	    if (l'==l) then c
	    else Evar (e,l')
      | Fix (ln,(lna,tl,bl)) ->
	  let tl' = Array.smartmap func tl in
	  let bl' = Array.smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else Fix (ln,(lna,tl',bl'))
      | CoFix(ln,(lna,tl,bl)) ->
	  let tl' = Array.smartmap func tl in
	  let bl' = Array.smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else CoFix (ln,(lna,tl',bl'))
      | _ -> c

let subst_mps sub c =
  if is_empty_subst sub then c
  else map_kn (subst_ind sub) (subst_con0 sub) c

let from_val a = ref (LSval a)
 
let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when ModPath.equal mp mpfrom -> mpto
    | MPdot (mp1,l) ->
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1==mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let rec mp_in_mp mp mp1 =
  match mp1 with
    | _ when ModPath.equal mp1 mp -> true
    | MPdot (mp2,l) -> mp_in_mp mp mp2
    | _ -> false

let subset_prefixed_by mp resolver =
  let mp_prefix mkey mequ rslv =
    if mp_in_mp mp mkey then Deltamap.add_mp mkey mequ rslv else rslv
  in
  let kn_prefix kn hint rslv =
    match hint with
      | Inline _ -> rslv
      | Equiv _ ->
	if mp_in_mp mp (modpath kn) then Deltamap.add_kn kn hint rslv else rslv
  in
  Deltamap.fold mp_prefix kn_prefix resolver empty_delta_resolver

let subst_dom_delta_resolver subst resolver =
  let mp_apply_subst mkey mequ rslv =
    Deltamap.add_mp (subst_mp subst mkey) mequ rslv
  in
  let kn_apply_subst kkey hint rslv =
    Deltamap.add_kn (subst_kn subst kkey) hint rslv
  in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver empty_delta_resolver

let subst_mp_delta sub mp mkey =
 match subst_mp0 sub mp with
    None -> empty_delta_resolver,mp
  | Some (mp',resolve) ->
      let mp1 = find_prefix resolve mp' in
      let resolve1 = subset_prefixed_by mp1 resolve in
      (subst_dom_delta_resolver
	 (map_mp mp1 mkey) resolve1),mp1

let gen_subst_delta_resolver dom subst resolver =
  let mp_apply_subst mkey mequ rslv =
    let mkey' = if dom then subst_mp subst mkey else mkey in
    let rslv',mequ' = subst_mp_delta subst mequ mkey in
    Deltamap.join rslv' (Deltamap.add_mp mkey' mequ' rslv)
  in
  let kn_apply_subst kkey hint rslv =
    let kkey' = if dom then subst_kn subst kkey else kkey in
    let hint' = match hint with
      | Equiv kequ -> Equiv (subst_kn_delta subst kequ)
      | Inline (lev,Some t) -> Inline (lev,Some (subst_mps subst t))
      | Inline (_,None) -> hint
    in
    Deltamap.add_kn kkey' hint' rslv
  in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver empty_delta_resolver

let subst_codom_delta_resolver = gen_subst_delta_resolver false
let subst_dom_codom_delta_resolver = gen_subst_delta_resolver true

let update_delta_resolver resolver1 resolver2 =
  let mp_apply_rslv mkey mequ rslv =
    if Deltamap.mem_mp mkey resolver2 then rslv
    else Deltamap.add_mp mkey (find_prefix resolver2 mequ) rslv
  in
  let kn_apply_rslv kkey hint rslv =
    if Deltamap.mem_kn kkey resolver2 then rslv
    else
      let hint' = match hint with
	| Equiv kequ -> Equiv (solve_delta_kn resolver2 kequ)
	| _ -> hint
      in
      Deltamap.add_kn kkey hint' rslv
  in
  Deltamap.fold mp_apply_rslv kn_apply_rslv resolver1 empty_delta_resolver

let add_delta_resolver resolver1 resolver2 =
  if resolver1 == resolver2 then
    resolver2
  else if Deltamap.is_empty resolver2 then
    resolver1
  else
    Deltamap.join (update_delta_resolver resolver1 resolver2) resolver2

let substition_prefixed_by k mp subst =
  let mp_prefixmp kmp (mp_to,reso) sub =
    if mp_in_mp mp kmp && not (ModPath.equal mp kmp) then
      let new_key = replace_mp_in_mp mp k kmp in
      Umap.add_mp new_key (mp_to,reso) sub
    else sub
  in
  let mbi_prefixmp mbi _ sub = sub
  in
  Umap.fold mp_prefixmp mbi_prefixmp subst empty_subst

let join subst1 subst2 =
  let apply_subst mpk add (mp,resolve) res =
    let mp',resolve' =
      match subst_mp0 subst2 mp with
	| None -> mp, None
	| Some (mp',resolve') ->  mp', Some resolve' in
    let resolve'' =
      match resolve' with
        | Some res ->
	    add_delta_resolver
	      (subst_dom_codom_delta_resolver subst2 resolve) res
	| None ->
	    subst_codom_delta_resolver subst2 resolve
    in
    let prefixed_subst = substition_prefixed_by mpk mp' subst2 in
    Umap.join prefixed_subst (add (mp',resolve'') res)
  in
  let mp_apply_subst mp = apply_subst mp (Umap.add_mp mp) in
  let mbi_apply_subst mbi = apply_subst (MPbound mbi) (Umap.add_mbi mbi) in
  let subst = Umap.fold mp_apply_subst mbi_apply_subst subst1 empty_subst in
  Umap.join subst2 subst

let force fsubst r =
  match !r with
  | LSval a -> a
  | LSlazy(s,a) ->
    match List.rev s with
      | [] -> assert false
      | sub0::subs ->
        let subst = List.fold_left join sub0 subs in
        let a' = fsubst subst a in
        r := LSval a';
        a'

let subst_substituted s r =
  match !r with
    | LSval a -> ref (LSlazy([s],a))
    | LSlazy(s',a) ->
	  ref (LSlazy(s::s',a))

let force_constr = force subst_mps

let from_val c = ref (LSval c)

let subst_constr_subst = subst_substituted

let subst_lazy_constr sub = function
  | Indirect (l,dp,i) -> Indirect (sub::l,dp,i)

let indirect_opaque_access =
  ref ((fun dp i -> assert false) : DirPath.t -> int -> constr)

let force_lazy_constr = function
  | Indirect (l,dp,i) ->
    let c = !indirect_opaque_access dp i in
    force_constr (List.fold_right subst_constr_subst l (from_val c))

let subst_constant_def sub = function
  | Undef inl -> Undef inl
  | Def c -> Def (subst_constr_subst sub c)
  | OpaqueDef lc ->
      OpaqueDef (Future.from_val (subst_lazy_constr sub (Future.join lc)))

type constant_constraints = Univ.constraints Future.computation

let body_of_constant cb = match cb.const_body with
  | Undef _ -> None
  | Def c -> Some (force_constr c)
  | OpaqueDef c -> Some (force_lazy_constr (Future.join c))

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Def _ | Undef _ -> false

let subst_rel_declaration sub (id,copt,t as x) =
  let copt' = Option.smartmap (subst_mps sub) copt in
  let t' = subst_mps sub t in
  if copt == copt' & t == t' then x else (id,copt',t')

let subst_rel_context sub = List.smartmap (subst_rel_declaration sub)

let subst_recarg sub r = match r with
  | Norec  -> r
  | (Mrec(kn,i)|Imbr (kn,i)) -> let kn' = subst_ind sub kn in
      if kn==kn' then r else Imbr (kn',i)

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

let subst_arity sub = function
| NonPolymorphicType s -> NonPolymorphicType (subst_mps sub s)
| PolymorphicArity (ctx,s) -> PolymorphicArity (subst_rel_context sub ctx,s)

(* TODO: should be changed to non-coping after Term.subst_mps *)
(* NB: we leave bytecode and native code fields untouched *)
let subst_const_body sub cb =
 { cb with
    const_body = subst_constant_def sub cb.const_body;
    const_type = subst_arity sub cb.const_type }

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
    mind_nf_lc = Array.smartmap (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_arity sub mbp.mind_arity;
    mind_user_lc = Array.smartmap (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealargs_ctxt = mbp.mind_nrealargs_ctxt;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }


let subst_mind sub mib =
  { mib with
    mind_params_ctxt = map_rel_context (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.smartmap (subst_mind_packet sub) mib.mind_packets }

(* Modules *)

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


