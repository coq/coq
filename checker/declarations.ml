open Util
open Names
open Cic
open Term

(** Substitutions, code imported from kernel/mod_subst *)

module Deltamap = struct
  [@@@ocaml.warning "-32-34"]
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
  [@@@ocaml.warning "-32-34"]
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
    let mp,dir,l = KerName.repr kn in
    let new_mp = find_prefix resolve mp in
    if mp == new_mp then
      kn
    else
      KerName.make new_mp dir l

let gen_of_delta resolve x kn fix_can =
  let new_kn = solve_delta_kn resolve kn in
  if kn == new_kn then x else fix_can new_kn

let constant_of_delta resolve con =
  let kn = Constant.user con in
  gen_of_delta resolve con kn (Constant.make kn)

let constant_of_delta2 resolve con =
  let kn, kn' = Constant.canonical con, Constant.user con in
  gen_of_delta resolve con kn (Constant.make kn')

let mind_of_delta resolve mind =
  let kn = MutInd.user mind in
  gen_of_delta resolve mind kn (MutInd.make kn)

let mind_of_delta2 resolve mind =
  let kn, kn' = MutInd.canonical mind, MutInd.user mind in
  gen_of_delta resolve mind kn (MutInd.make kn')

let find_inline_of_delta kn resolve =
  match Deltamap.find_kn kn resolve with
    | Inline (_,o) -> o
    | _ -> raise Not_found

let constant_of_delta_with_inline resolve con =
  let kn1,kn2 = Constant.canonical con, Constant.user con in
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
 let mp,dir,l = KerName.repr kn in
  match subst_mp0 sub mp with
     Some (mp',resolve) ->
      solve_delta_kn resolve (KerName.make mp' dir l)
   | None -> kn

let subst_kn sub kn =
 let mp,dir,l = KerName.repr kn in
  match subst_mp0 sub mp with
     Some (mp',_) ->
      KerName.make mp' dir l
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
  let knu = KerName.make mpu dir l in
  if mpu == mpc then MutInd.make1 knu
  else MutInd.make knu (KerName.make mpc dir l)

let subst_ind sub mind =
  let kn1,kn2 = MutInd.user mind, MutInd.canonical mind in
  let mp1,dir,l = KerName.repr kn1 in
  let mp2,_,_ = KerName.repr kn2 in
  let rebuild_mind mp1 mp2 = make_mind_equiv mp1 mp2 dir l in
  try
    let side,mind',resolve = gen_subst_mp rebuild_mind sub mp1 mp2 in
    match side with
      | User -> mind_of_delta resolve mind'
      | Canonical -> mind_of_delta2 resolve mind'
  with No_subst -> mind

let make_con_equiv mpu mpc dir l =
  let knu = KerName.make mpu dir l in
  if mpu == mpc then Constant.make1 knu
  else Constant.make knu (KerName.make mpc dir l)

let subst_con0 sub con u =
  let kn1,kn2 = Constant.user con, Constant.canonical con in
  let mp1,dir,l = KerName.repr kn1 in
  let mp2,_,_ = KerName.repr kn2 in
  let rebuild_con mp1 mp2 = make_con_equiv mp1 mp2 dir l in
  let dup con = con, Const (con, u) in
  let side,con',resolve = gen_subst_mp rebuild_con sub mp1 mp2 in
  match constant_of_delta_with_inline resolve con' with
    | Some (ctx, t) ->
      (** FIXME: we never typecheck the inlined term, so that it could well
          be garbage. What environment do we type it in though? The substitution
          code should be moot in the checker but it **is** used nonetheless. *)
      let () = assert (Univ.AUContext.size ctx == Univ.Instance.length u) in
      con', subst_instance_constr u t
    | None ->
      let con'' = match side with
	| User -> constant_of_delta resolve con'
	| Canonical -> constant_of_delta2 resolve con'
      in
      if con'' == con then raise No_subst else dup con''

let rec map_kn f f' c =
  let func = map_kn f f' in
    match c with
      | Const (kn, u) -> (try snd (f' kn u) with No_subst -> c)
      | Proj (p,t) -> 
          let p' = Projection.map f p in
	  let t' = func t in
	    if p' == p && t' == t then c
	    else Proj (p', t')
      | Ind ((kn,i),u) ->
	  let kn' = f kn in
	  if kn'==kn then c else Ind ((kn',i),u)
      | Construct (((kn,i),j),u) ->
	  let kn' = f kn in
	  if kn'==kn then c else Construct (((kn',i),j),u)
      | Case (ci,p,ct,l) ->
	  let ci_ind =
            let (kn,i) = ci.ci_ind in
	    let kn' = f kn in
	    if kn'==kn then ci.ci_ind else kn',i
	  in
	  let p' = func p in
	  let ct' = func ct in
          let l' = Array.Smart.map func l in
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
          let l' = Array.Smart.map func l in
	    if (ct'== ct && l'==l) then c
	    else App (ct',l')
      | Evar (e,l) ->
          let l' = Array.Smart.map func l in
	    if (l'==l) then c
	    else Evar (e,l')
      | Fix (ln,(lna,tl,bl)) ->
          let tl' = Array.Smart.map func tl in
          let bl' = Array.Smart.map func bl in
	    if (bl == bl'&& tl == tl') then c
	    else Fix (ln,(lna,tl',bl'))
      | CoFix(ln,(lna,tl,bl)) ->
          let tl' = Array.Smart.map func tl in
          let bl' = Array.Smart.map func bl in
	    if (bl == bl'&& tl == tl') then c
	    else CoFix (ln,(lna,tl',bl'))
      | _ -> c

let subst_mps sub c =
  if is_empty_subst sub then c
  else map_kn (subst_ind sub) (subst_con0 sub) c
 
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
	if mp_in_mp mp (KerName.modpath kn)
        then Deltamap.add_kn kn hint rslv
        else rslv
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
      | Inline (lev,Some (ctx, t)) -> Inline (lev,Some (ctx, subst_mps subst t))
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

let from_val x = { subst_value = x; subst_subst = []; }

let force fsubst r = match r.subst_subst with
| [] -> r.subst_value
| s ->
  let subst = List.fold_left join empty_subst (List.rev s) in
  let x = fsubst subst r.subst_value in
  let () = r.subst_subst <- [] in
  let () = r.subst_value <- x in
  x

let subst_substituted s r = { r with subst_subst = s :: r.subst_subst; }

let force_constr = force subst_mps

let subst_constr_subst = subst_substituted

let subst_lazy_constr sub = function
  | Indirect (l,dp,i) -> Indirect (sub::l,dp,i)

let indirect_opaque_access =
  ref ((fun dp i -> assert false) : DirPath.t -> int -> constr)
let indirect_opaque_univ_access =
  ref ((fun dp i -> assert false) : DirPath.t -> int -> Univ.ContextSet.t)

let force_lazy_constr = function
  | Indirect (l,dp,i) ->
    let c = !indirect_opaque_access dp i in
    force_constr (List.fold_right subst_constr_subst l (from_val c))

let force_lazy_constr_univs = function
  | OpaqueDef (Indirect (l,dp,i)) -> !indirect_opaque_univ_access dp i
  | _ -> Univ.ContextSet.empty

let subst_constant_def sub = function
  | Undef inl -> Undef inl
  | Def c -> Def (subst_constr_subst sub c)
  | OpaqueDef lc -> OpaqueDef (subst_lazy_constr sub lc)

(** Local variables and graph *)

let body_of_constant cb = match cb.const_body with
  | Undef _ -> None
  | Def c -> Some (force_constr c)
  | OpaqueDef c -> Some (force_lazy_constr c)

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Def _ | Undef _ -> false

let opaque_univ_context cb = force_lazy_constr_univs cb.const_body

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

let subst_wf_paths sub p = Rtree.Smart.map (subst_recarg sub) p

let eq_recarg r1 r2 = match r1, r2 with
  | Norec, Norec -> true
  | Mrec i1, Mrec i2 -> Names.eq_ind_chk i1 i2
  | Imbr i1, Imbr i2 -> Names.eq_ind_chk i1 i2
  | _ -> false

let eq_wf_paths = Rtree.equal eq_recarg

let inductive_make_projections ind mib =
  match mib.mind_record with
  | NotRecord | FakeRecord -> None
  | PrimRecord infos ->
    let projs = Array.mapi (fun proj_arg lab ->
        Names.Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg lab)
        (pi2 infos.(snd ind))
    in
    Some projs

(**********************************************************************)
(* Representation of mutual inductive types in the kernel             *)
(*
   Inductive I1 (params) : U1 := c11 : T11 | ... | c1p1 : T1p1
   ...
   with      In (params) : Un := cn1 : Tn1 | ... | cnpn : Tnpn
*)


let subst_decl_arity f g sub ar = 
  match ar with
  | RegularArity x -> 
    let x' = f sub x in 
      if x' == x then ar
      else RegularArity x'
  | TemplateArity x -> 
    let x' = g sub x in 
      if x' == x then ar
      else TemplateArity x'

let subst_rel_declaration sub =
  Term.map_rel_decl (subst_mps sub)

let subst_rel_context sub = List.Smart.map (subst_rel_declaration sub)

let constant_is_polymorphic cb =
  match cb.const_universes with
  | Monomorphic_const _ -> false
  | Polymorphic_const _ -> true

(* TODO: should be changed to non-coping after Term.subst_mps *)
(* NB: we leave bytecode and native code fields untouched *)
let subst_const_body sub cb =
 { cb with
    const_body = subst_constant_def sub cb.const_body;
    const_type = subst_mps sub cb.const_type }


let subst_regular_ind_arity sub s =
  let uar' = subst_mps sub s.mind_user_arity in
    if uar' == s.mind_user_arity then s 
    else { mind_user_arity = uar'; mind_sort = s.mind_sort }

let subst_template_ind_arity sub s = s

(* FIXME records *)
let subst_ind_arity =
  subst_decl_arity subst_regular_ind_arity subst_template_ind_arity

let subst_mind_packet sub mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.Smart.map (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_ind_arity sub mbp.mind_arity;
    mind_user_lc = Array.Smart.map (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealdecls = mbp.mind_nrealdecls;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }


let subst_mind sub mib =
  { mib with
    mind_params_ctxt = map_rel_context (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.Smart.map (subst_mind_packet sub) mib.mind_packets }

(* Modules *)

let rec functor_map fty f0 = function
  | NoFunctor a -> NoFunctor (f0 a)
  | MoreFunctor (mbid,ty,e) -> MoreFunctor(mbid,fty ty,functor_map fty f0 e)

let implem_map fs fa = function
  | Struct s -> Struct (fs s)
  | Algebraic a -> Algebraic (fa a)
  | impl -> impl

let rec subst_expr sub = function
  | MEident mp -> MEident (subst_mp sub mp)
  | MEapply (me1,mp2)-> MEapply (subst_expr sub me1, subst_mp sub mp2)
  | MEwith (me,wd)-> MEwith (subst_expr sub me, wd)

let rec subst_expression sub me =
  functor_map (subst_module_type sub) (subst_expr sub) me

and subst_signature sub sign =
  functor_map (subst_module_type sub) (subst_structure sub) sign

and subst_structure sub struc =
  let subst_body = function
    | SFBconst cb -> SFBconst (subst_const_body sub cb)
    | SFBmind mib -> SFBmind (subst_mind sub mib)
    | SFBmodule mb -> SFBmodule (subst_module sub mb)
    | SFBmodtype mtb -> SFBmodtype (subst_module_type sub mtb)
  in
  List.map (fun (l,b) -> (l,subst_body b)) struc

and subst_body : 'a. (_ -> 'a -> 'a) -> _ -> 'a generic_module_body -> 'a generic_module_body =
  fun subst_impl sub mb ->
  { mb with
    mod_mp = subst_mp sub mb.mod_mp;
    mod_expr = subst_impl sub mb.mod_expr;
    mod_type = subst_signature sub mb.mod_type;
    mod_type_alg = Option.Smart.map (subst_expression sub) mb.mod_type_alg }

and subst_module sub mb =
  subst_body (fun sub e -> implem_map (subst_signature sub) (subst_expression sub) e) sub mb

and subst_module_type sub mb =
  subst_body (fun _ () -> ()) sub mb
