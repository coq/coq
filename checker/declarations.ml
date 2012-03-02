open Errors
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

(** Substitutions, code imported from kernel/mod_subst *)

type delta_hint =
  | Inline of int * constr option
  | Equiv of kernel_name


module Deltamap = struct
  type t = module_path MPmap.t * delta_hint KNmap.t
  let empty = MPmap.empty, KNmap.empty
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

type delta_resolver = Deltamap.t

let empty_delta_resolver = Deltamap.empty

module MBImap = Map.Make
  (struct
    type t = mod_bound_id
    let compare = Pervasives.compare
   end)

module Umap = struct
  type 'a t = 'a MPmap.t * 'a MBImap.t
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

type substitution = (module_path * delta_resolver) Umap.t
type 'a subst_fun = substitution -> 'a -> 'a

let empty_subst = Umap.empty

let is_empty_subst = Umap.is_empty

let val_delta_hint =
  val_sum "delta_hint" 0
    [|[|val_int; val_opt val_constr|];[|val_kn|]|]

let val_res =
  val_tuple ~name:"delta_resolver"
    [|val_map ~name:"delta_resolver" val_mp val_mp;
      val_map ~name:"delta_resolver" val_kn val_delta_hint|]

let val_mp_res = val_tuple [|val_mp;val_res|]

let val_subst =
  val_tuple ~name:"substitution"
    [|val_map ~name:"substitution" val_mp val_mp_res;
      val_map ~name:"substitution" val_uid val_mp_res|]

let add_mbid mbid mp = Umap.add_mbi mbid (mp,empty_delta_resolver)
let add_mp mp1 mp2 = Umap.add_mp mp1 (mp2,empty_delta_resolver)

let map_mbid mbid mp = add_mbid mbid mp empty_subst
let map_mp mp1 mp2 = add_mp mp1 mp2 empty_subst

let mp_in_delta mp =
  Deltamap.mem_mp mp

let rec find_prefix resolve mp =
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
  try
    let new_kn = solve_delta_kn resolve kn in
    if kn == new_kn then x else fix_can new_kn
  with _ -> x

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

let subst_mps sub c =
  if is_empty_subst sub then c
  else map_kn (subst_ind sub) (subst_con0 sub) c


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
  else if resolver2 = empty_delta_resolver then
    resolver1
  else
    Deltamap.join (update_delta_resolver resolver1 resolver2) resolver2

let substition_prefixed_by k mp subst =
  let mp_prefixmp kmp (mp_to,reso) sub =
    if mp_in_mp mp kmp && mp <> kmp then
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

(** Beware! In .vo files, lazy_constr are stored as integers
   used as indexes for a separate table. The actual lazy_constr is restored
   later, by [Safe_typing.LightenLibrary.load]. This allows us
   to use here a different definition of lazy_constr than coqtop:
   since the checker will inspect all proofs parts, even opaque
   ones, no need to use Lazy.t here *)

type lazy_constr = constr_substituted
let subst_lazy_constr = subst_substituted
let force_lazy_constr = force_constr
let lazy_constr_from_val c = c
let val_lazy_constr = val_cstr_subst

(** Inlining level of parameters at functor applications.
    This is ignored by the checker. *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

type constant_def =
  | Undef of inline
  | Def of constr_substituted
  | OpaqueDef of lazy_constr

let val_cst_def =
  val_sum "constant_def" 0
    [|[|val_opt val_int|]; [|val_cstr_subst|]; [|val_lazy_constr|]|]

let subst_constant_def sub = function
  | Undef inl -> Undef inl
  | Def c -> Def (subst_constr_subst sub c)
  | OpaqueDef lc -> OpaqueDef (subst_lazy_constr sub lc)

type constant_body = {
    const_hyps : section_context; (* New: younger hyp at top *)
    const_body : constant_def;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
    const_constraints : Univ.constraints }

let body_of_constant cb = match cb.const_body with
  | Undef _ -> None
  | Def c -> Some c
  | OpaqueDef c -> Some c

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Def _ | Undef _ -> false

let val_cb = val_tuple ~name:"constant_body"
  [|val_nctxt;
    val_cst_def;
    val_cst_type;
    no_val;
    val_cstrs|]

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
    const_body = subst_constant_def sub cb.const_body;
    const_type = subst_arity sub cb.const_type;
    const_body_code = (*Cemitcodes.subst_to_patch_subst sub*) cb.const_body_code;
    const_constraints = cb.const_constraints}

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


