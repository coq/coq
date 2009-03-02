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
  val_tuple"polyorphic_arity"[|val_list(val_opt val_univ);val_univ|]

type constant_type =
  | NonPolymorphicType of constr
  | PolymorphicArity of rel_context * polymorphic_arity

let val_cst_type =
  val_sum "constant_type" 0 [|[|val_constr|];[|val_rctxt;val_pol_arity|]|]


type substitution_domain = 
    MSI of mod_self_id 
  | MBI of mod_bound_id
  | MPI of module_path

let val_subst_dom =
  val_sum "substitution_domain" 0 [|[|val_uid|];[|val_uid|];[|val_mp|]|]

module Umap = Map.Make(struct 
			 type t = substitution_domain
			 let compare = Pervasives.compare
		       end)

type resolver

type substitution = (module_path * resolver option) Umap.t
type 'a subst_fun = substitution -> 'a -> 'a

let val_res = val_opt no_val

let val_subst =
  val_map ~name:"substitution"
    val_subst_dom (val_tuple "substition range" [|val_mp;val_res|])


let fold_subst fs fb fp =
  Umap.fold
    (fun k (mp,_) acc ->
      match k with
          MSI msid -> fs msid mp acc
        | MBI mbid -> fb mbid mp acc
        | MPI mp1 -> fp mp1 mp acc)

let empty_subst = Umap.empty

let add_msid msid mp =
  Umap.add (MSI msid) (mp,None)
let add_mbid mbid mp =
  Umap.add (MBI mbid) (mp,None)
let add_mp mp1 mp2  =
  Umap.add (MPI mp1) (mp2,None)

let map_msid msid mp = add_msid msid mp empty_subst
let map_mbid mbid mp = add_mbid mbid mp empty_subst
let map_mp mp1 mp2 = add_mp mp1 mp2 empty_subst

let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPself sid -> 
        let mp',resolve = Umap.find (MSI sid) sub in
         mp',resolve
    | MPbound bid ->
        let mp',resolve = Umap.find (MBI bid) sub in
          mp',resolve
    | MPdot (mp1,l) as mp2 ->
	begin
	  try  
	    let mp',resolve = Umap.find (MPI mp2) sub in
              mp',resolve
	  with Not_found ->    
	    let mp1',resolve = aux mp1 in
	      MPdot (mp1',l),resolve
	end
    | _ -> raise Not_found
 in
  try
    Some (aux mp) 
  with Not_found -> None



let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPself sid -> fst (Umap.find (MSI sid) sub)
    | MPbound bid -> fst (Umap.find (MBI bid) sub)
    | MPdot (mp1,l) as mp2 ->
	begin
	  try fst (Umap.find (MPI mp2) sub)
	  with Not_found -> MPdot (aux mp1,l)
	end

    | _ -> raise Not_found
 in
  try Some (aux mp) with Not_found -> None

let subst_mp sub mp =
 match subst_mp0 sub mp with
    None -> mp
  | Some mp' -> mp'

let subst_kn0 sub kn =
 let mp,dir,l = repr_kn kn in
  match subst_mp0 sub mp with
     Some mp' ->
      Some (make_kn mp' dir l)
   | None -> None

let subst_kn sub kn =
 match subst_kn0 sub kn with
    None -> kn
  | Some kn' -> kn'

let subst_con sub con =
 let mp,dir,l = repr_con con in
  match subst_mp0 sub mp with
     None -> con
   | Some mp' -> make_con mp' dir l

let subst_con0 sub con =
 let mp,dir,l = repr_con con in
  match subst_mp0 sub mp with
      None -> None
    | Some mp' ->
	let con' = make_con mp' dir l in
        Some (Const con')

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
  map_kn (subst_kn0 sub) (subst_con0 sub)

let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when mp = mpfrom -> mpto
    | MPdot (mp1,l) -> 
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1==mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let replace_mp_in_con mpfrom mpto kn =
 let mp,dir,l = kn in
  let mp'' = replace_mp_in_mp mpfrom mpto mp in
    if mp==mp'' then kn
    else (mp'', dir, l)

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



let join (subst1 : substitution) (subst2 : substitution) =
  let apply_subst (sub : substitution) key (mp,_) =
      match subst_mp0 sub mp with
	  None -> mp,None
	| Some mp' -> mp',None in
  let subst = Umap.mapi (apply_subst subst2) subst1 in
    (Umap.fold Umap.add subst2 subst)

let subst_key subst1 subst2 =
  let replace_in_key key mp sub=
    let newkey = 
      match key with
	| MPI mp1 -> 
	    begin
	      match subst_mp0 subst1 mp1 with
		| None -> None
		| Some mp2 -> Some (MPI mp2)
	    end
	| _ -> None
    in
      match newkey with
	| None -> Umap.add key mp sub
	| Some mpi -> Umap.add mpi mp sub
  in
    Umap.fold replace_in_key subst2 empty_subst

let update_subst_alias subst1 subst2 =
 let subst_inv key (mp,_) sub =
    let newmp = 
      match key with 
	| MBI msid -> Some (MPbound msid)
	| MSI msid -> Some (MPself msid)
	| _ -> None
    in
      match newmp with
	| None -> sub
	| Some mpi -> match mp with 
	    | MPbound mbid -> Umap.add (MBI mbid) (mpi,None) sub
	    | MPself msid -> Umap.add (MSI msid) (mpi,None) sub
	    | _ ->  Umap.add (MPI mp) (mpi,None) sub
  in 
  let subst_mbi = Umap.fold subst_inv subst2 empty_subst in
  let alias_subst key (mp,_) sub=
    let newkey = 
      match key with
	| MPI mp1 -> 
	    begin
	      match subst_mp0 subst_mbi mp1 with
		| None -> None
		| Some mp2 -> Some (MPI mp2)
	    end
	| _ -> None
    in
      match newkey with
	| None -> Umap.add key (mp,None) sub
	| Some mpi -> Umap.add mpi (mp,None) sub
  in
    Umap.fold alias_subst subst1 empty_subst

let join_alias (subst1 : substitution) (subst2 : substitution) =
  let apply_subst (sub : substitution) key (mp,_) =
      match subst_mp0 sub mp with
	  None -> mp,None
	| Some mp' -> mp',None in
  Umap.mapi (apply_subst subst2) subst1 


let update_subst subst1 subst2 =
 let subst_inv key (mp,_) l =
    let newmp = 
      match key with 
	| MBI msid -> MPbound msid
	| MSI msid -> MPself msid
	| MPI mp -> mp
    in
   match mp with 
     | MPbound mbid ->  ((MBI mbid),newmp)::l
     | MPself msid ->  ((MSI msid),newmp)::l
     | _ ->   ((MPI mp),newmp)::l
  in 
  let subst_mbi = Umap.fold subst_inv subst2 [] in
  let alias_subst key (mp,_) sub=
    let newsetkey = 
      match key with
	| MPI mp1 -> 
	    let compute_set_newkey l (k,mp') = 
	      let mp_from_key = match k with
		  	| MBI msid -> MPbound msid
			| MSI msid -> MPself msid
			| MPI mp -> mp
	      in
	      let new_mp1 = replace_mp_in_mp mp_from_key mp' mp1 in
		if new_mp1 == mp1 then l else (MPI new_mp1)::l
	    in
	    begin
	      match List.fold_left compute_set_newkey [] subst_mbi with
		| [] -> None
		| l -> Some (l)
	    end
	| _ -> None
    in
      match newsetkey with
	| None -> sub
	| Some l -> 
	    List.fold_left (fun s k -> Umap.add k (mp,None) s)
	      sub l
  in
    Umap.fold alias_subst subst1 empty_subst


let subst_substituted s r =
  match !r with
    | LSval a -> ref (LSlazy(s,a))
    | LSlazy(s',a) ->
	let s'' = join s' s in
	  ref (LSlazy(s'',a))

let force_constr = force subst_mps 

type constr_substituted = constr substituted

let val_cstr_subst =
  val_ref
    (val_sum "constr_substituted" 0
      [|[|val_constr|];[|val_subst;val_constr|]|])

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

let val_cb = val_tuple "constant_body"
  [|val_nctxt;val_opt val_cstr_subst; val_cst_type;no_val;val_cstrs;
    val_bool; val_bool |]


let subst_rel_declaration sub (id,copt,t as x) =
  let copt' = Option.smartmap (subst_mps sub) copt in
  let t' = subst_mps sub t in
  if copt == copt' & t == t' then x else (id,copt',t')

let subst_rel_context sub = list_smartmap (subst_rel_declaration sub)

type recarg = 
  | Norec 
  | Mrec of int 
  | Imbr of inductive
let val_recarg = val_sum "recarg" 1 (* Norec *)
  [|[|val_int|] (* Mrec *);[|val_ind|] (* Imbr *)|]

let subst_recarg sub r = match r with
  | Norec | Mrec _  -> r
  | Imbr (kn,i) -> let kn' = subst_kn sub kn in
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
  val_tuple"monomorphic_inductive_arity"[|val_constr;val_sort|]

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

let val_one_ind = val_tuple "one_inductive_body"
  [|val_id;val_rctxt;val_ind_arity;val_array val_id;val_array val_constr;
    val_int; val_list val_sortfam;val_array val_constr;val_array val_int;
    val_wfp; val_int; val_int; no_val|]


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

  (* Source of the inductive block when aliased in a module *)
    mind_equiv : kernel_name option
  }
let val_ind_pack = val_tuple "mutual_inductive_body"
  [|val_array val_one_ind;val_bool;val_bool;val_int;val_nctxt;
    val_int; val_int; val_rctxt;val_cstrs;val_opt val_kn|]


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
    mind_constraints = mib.mind_constraints ;
    mind_equiv = Option.map (subst_kn sub) mib.mind_equiv }

(* Modules *)

(* Whenever you change these types, please do update the validation
   functions below *)
type structure_field_body = 
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBalias of module_path * struct_expr_body option * Univ.constraints option
  | SFBmodtype of module_type_body

and structure_body = (label * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of mod_bound_id * module_type_body * struct_expr_body 
  | SEBstruct of mod_self_id * structure_body
  | SEBapply of struct_expr_body * struct_expr_body
      * Univ.constraints
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of identifier list * module_path *
      struct_expr_body option * Univ.constraints
  | With_definition_body of  identifier list * constant_body
        
and module_body = 
    { mod_expr : struct_expr_body option;
      mod_type : struct_expr_body option;
      mod_constraints : Univ.constraints;
      mod_alias : substitution;
      mod_retroknowledge : action list}

and module_type_body = 
    { typ_expr : struct_expr_body;
      typ_strength : module_path option;
      typ_alias : substitution}

(* the validation functions: *)
let rec val_sfb o = val_sum "struct_field_body" 0
  [|[|val_cb|];       (* SFBconst *)
    [|val_ind_pack|]; (* SFBmind *)
    [|val_module|];   (* SFBmodule *)
    [|val_mp;val_opt val_seb;val_opt val_cstrs|]; (* SFBalias *)
    [|val_modtype|]   (* SFBmodtype *)
  |] o
and val_sb o = val_list (val_tuple"label*sfb"[|val_id;val_sfb|]) o
and val_seb o = val_sum "struct_expr_body" 0
  [|[|val_mp|];                      (* SEBident *)
    [|val_uid;val_modtype;val_seb|]; (* SEBfunctor *)
    [|val_uid;val_sb|];              (* SEBstruct *)
    [|val_seb;val_seb;val_cstrs|];   (* SEBapply *)
    [|val_seb;val_with|]             (* SEBwith *)
  |] o
and val_with o = val_sum "with_declaration_body" 0
  [|[|val_list val_id;val_mp;val_cstrs|];
    [|val_list val_id;val_cb|]|] o
and val_module o = val_tuple "module_body"
  [|val_opt val_seb;val_opt val_seb;val_cstrs;val_subst;no_val|] o
and val_modtype o = val_tuple "module_type_body"
  [|val_seb;val_opt val_mp;val_subst|] o

	
let rec subst_with_body sub = function
  | With_module_body(id,mp,typ_opt,cst) ->
      With_module_body(id,subst_mp sub mp,
		       Option.smartmap (subst_struct_expr sub) typ_opt,cst)
  | With_definition_body(id,cb) ->
      With_definition_body( id,subst_const_body sub cb)

and subst_modtype sub mtb =
  let typ_expr' = subst_struct_expr sub mtb.typ_expr in
    if typ_expr'==mtb.typ_expr then
      mtb
    else
      { mtb with 
	  typ_expr = typ_expr'}
	
and subst_structure sub sign = 
  let subst_body  = function
      SFBconst cb -> 
	SFBconst (subst_const_body sub cb)
    | SFBmind mib -> 
	SFBmind (subst_mind sub mib)
    | SFBmodule mb -> 
	SFBmodule (subst_module sub mb)
    | SFBmodtype mtb -> 
	SFBmodtype (subst_modtype sub mtb)
 | SFBalias (mp,typ_opt ,cst) ->
	SFBalias (subst_mp sub mp,
		  Option.smartmap (subst_struct_expr sub) typ_opt,cst)
  in
    List.map (fun (l,b) -> (l,subst_body b)) sign

and subst_module  sub mb =
  let mtb' = Option.smartmap (subst_struct_expr sub) mb.mod_type in
  (* This is similar to the previous case. In this case we have
     a module M in a signature that is knows to be equivalent to a module M'
     (because the signature is "K with Module M := M'") and we are substituting
     M' with some M''. *)
  let me' = Option.smartmap (subst_struct_expr sub) mb.mod_expr in
  let mb_alias = join_alias mb.mod_alias sub in
    if mtb'==mb.mod_type && mb.mod_expr == me' 
      && mb_alias == mb.mod_alias
    then mb else
      { mod_expr = me';
	mod_type=mtb'; 
	mod_constraints=mb.mod_constraints;
	mod_alias = mb_alias;
	mod_retroknowledge=mb.mod_retroknowledge}


and subst_struct_expr sub = function
    | SEBident mp -> SEBident (subst_mp sub  mp)
    | SEBfunctor (msid, mtb, meb') -> 
	SEBfunctor(msid,subst_modtype sub mtb,subst_struct_expr sub meb')
    | SEBstruct (msid,str)->
	SEBstruct(msid, subst_structure sub str)
    | SEBapply (meb1,meb2,cst)->
	SEBapply(subst_struct_expr sub meb1,
		 subst_struct_expr sub meb2,
		 cst)
    | SEBwith (meb,wdb)-> 
	SEBwith(subst_struct_expr sub meb,
		subst_with_body sub wdb)
 

let subst_signature_msid msid mp = 
  subst_structure (map_msid msid mp)
