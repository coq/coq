open Names
open Declarations
open Term
open Vm
open Environ
open Conv_oracle
open Reduction 
open Closure
open Vm
open Csymtable
open Univ
open Cbytecodes



(* Test la structure des piles *)

let compare_zipper z1 z2 =
  match z1, z2 with
  | Zapp args1, Zapp args2 -> nargs args1 = nargs args2
  | Zfix _, Zfix _ -> true 
  | Zswitch _, Zswitch _ -> true
  | _ , _ -> false

let rec compare_stack stk1 stk2 =
  match stk1, stk2 with
  | [], [] -> true
  | z1::stk1, z2::stk2 ->
      if compare_zipper z1 z2 then compare_stack stk1 stk2
      else false
  | _, _ -> false 

(* Conversion *)
let conv_vect fconv vect1 vect2 cu =
  let n = Array.length vect1 in
  if n = Array.length vect2 then
    let rcu = ref cu in
    for i = 0 to n - 1 do
      rcu := fconv vect1.(i) vect2.(i) !rcu
    done;
    !rcu
  else raise NotConvertible

let infos = ref (create_clos_infos betaiotazeta Environ.empty_env)

let rec conv_val pb k v1 v2 cu =
  if v1 == v2 then cu else conv_whd pb k (whd_val v1) (whd_val v2) cu 
    
and conv_whd pb k whd1 whd2 cu =  
  match whd1, whd2 with
  | Vsort s1, Vsort s2 -> sort_cmp pb s1 s2 cu 
  | Vprod p1, Vprod p2 ->
      let cu = conv_val CONV k (dom p1) (dom p2) cu in
      conv_fun pb k (codom p1) (codom p2) cu
  | Vfun f1, Vfun f2 -> conv_fun CONV k f1 f2 cu
  | Vfix f1, Vfix f2 -> conv_fix k f1 f2 cu
  | Vfix_app fa1, Vfix_app fa2 ->
      let f1 = fix fa1 in
      let args1 = args_of_fix fa1 in
      let f2 = fix fa2 in
      let args2 = args_of_fix fa2 in
      conv_arguments k args1 args2 (conv_fix k f1 f2 cu)
  | Vcofix cf1, Vcofix cf2 -> 
      conv_cofix k cf1 cf2 cu
  | Vcofix_app cfa1, Vcofix_app cfa2 ->	
      let cf1 = cofix cfa1 in
      let args1 = args_of_cofix cfa1 in
      let cf2 = cofix cfa2 in
      let args2 = args_of_cofix cfa2 in
      conv_arguments k args1 args2 (conv_cofix k cf1 cf2 cu)
  | Vconstr_const i1, Vconstr_const i2 -> 
      if i1 = i2 then cu else raise NotConvertible 
  | Vconstr_block b1, Vconstr_block b2 ->
      let sz = bsize b1 in
      if btag b1 = btag b2 && sz = bsize b2 then
	let rcu = ref cu in
	for i = 0 to sz - 1 do
	  rcu := conv_val CONV k (bfield b1 i) (bfield b2 i) !rcu
	done;
	!rcu
      else raise NotConvertible
  | Vatom_stk(a1,stk1), Vatom_stk(a2,stk2) -> 
      conv_atom pb k a1 stk1 a2 stk2 cu
  | _, Vatom_stk(Aiddef(_,v) as a2,stk) -> 
      conv_whd pb k whd1 (force_whd v stk) cu
  | Vatom_stk(Aiddef(_,v) as a1,stk), _ -> 
      conv_whd pb k (force_whd v stk) whd2 cu
  | _, _ -> raise NotConvertible

and conv_atom pb k a1 stk1 a2 stk2 cu =
  match a1, a2 with
  | Aind (kn1,i1), Aind(kn2,i2) ->
      if i1 = i2 && mind_equiv !infos kn1 kn2 && compare_stack stk1 stk2 then
	conv_stack k stk1 stk2 cu
      else raise NotConvertible
  | Aid ik1, Aid ik2 -> 
      if ik1 = ik2 && compare_stack stk1 stk2 then 
	conv_stack k stk1 stk2 cu 
      else raise NotConvertible
  | Aiddef(ik1,v1), Aiddef(ik2,v2) ->
      begin
	try
	  if ik1 = ik2 && compare_stack stk1 stk2 then
	    conv_stack k stk1 stk2 cu 
	  else raise NotConvertible
	with NotConvertible ->
	  if oracle_order ik1 ik2 then             
            conv_whd pb k (whd_stack v1 stk1) (Vatom_stk(a2,stk2)) cu
          else conv_whd pb k (Vatom_stk(a1,stk1)) (whd_stack v2 stk2) cu
      end
  | Aiddef(ik1,v1), _ ->
      conv_whd pb k (force_whd v1 stk1) (Vatom_stk(a2,stk2)) cu
  | _, Aiddef(ik2,v2) ->
      conv_whd pb k (Vatom_stk(a1,stk1)) (force_whd v2 stk2) cu
  | Afix_app _, _ | _, Afix_app _ | Aswitch _, _ | _, Aswitch _ -> 
      Util.anomaly "Vconv.conv_atom : Vm.whd_val doesn't work"
  | _, _ -> raise NotConvertible 
	
and conv_stack k stk1 stk2 cu =
  match stk1, stk2 with
  | [], [] -> cu
  | Zapp args1 :: stk1, Zapp args2 :: stk2 ->
      conv_stack k stk1 stk2 (conv_arguments k args1 args2 cu) 
  | Zfix fa1 :: stk1, Zfix fa2 :: stk2 ->
      let f1 = fix fa1 in
      let args1 = args_of_fix fa1 in
      let f2 = fix fa2 in
      let args2 = args_of_fix fa2 in
      conv_stack k stk1 stk2 
	(conv_arguments k args1 args2 (conv_fix k f1 f2 cu))
  | Zswitch sw1 :: stk1, Zswitch sw2 :: stk2 ->
      if eq_tbl sw1 sw2 then
	let vt1,vt2 = type_of_switch sw1, type_of_switch sw2 in
	let rcu = ref (conv_val CONV k vt1 vt2 cu) in
	let b1, b2 = branch_of_switch k sw1, branch_of_switch k sw2 in
	for i = 0 to Array.length b1 - 1 do
	  rcu := 
	    conv_val CONV (k + fst b1.(i)) 
	      (snd b1.(i)) (snd b2.(i)) !rcu
	done;
	conv_stack k stk1 stk2 !rcu
      else raise NotConvertible
  | _, _ -> raise NotConvertible

and conv_fun pb k f1 f2 cu =
  if f1 == f2 then cu
  else
    let arity,b1,b2 = decompose_vfun2 k f1 f2 in
    conv_val pb (k+arity) b1 b2 cu

and conv_fix k f1 f2 cu =
  if f1 == f2 then cu 
  else
    if check_fix f1 f2 then
      let tf1 = types_of_fix f1 in
      let tf2 = types_of_fix f2 in
      let cu = conv_vect (conv_val CONV k) tf1 tf2 cu in
      let bf1 = bodies_of_fix k f1 in
      let bf2 = bodies_of_fix k f2 in
      conv_vect (conv_fun CONV (k + (fix_ndef f1))) bf1 bf2 cu
    else raise NotConvertible

and conv_cofix k cf1 cf2 cu =
  if cf1 == cf2 then cu
  else
    if check_cofix cf1 cf2 then
      let tcf1 = types_of_cofix cf1 in
      let tcf2 = types_of_cofix cf2 in
      let cu = conv_vect (conv_val CONV k) tcf1 tcf2 cu in
      let bcf1 = bodies_of_cofix k cf1 in
      let bcf2 = bodies_of_cofix k cf2 in
      conv_vect (conv_val CONV (k + (cofix_ndef cf1))) bcf1 bcf2 cu
    else raise NotConvertible

and conv_arguments k args1 args2 cu =
  if args1 == args2 then cu
  else
    let n = nargs args1 in
    if n = nargs args2 then
      let rcu = ref cu in
      for i = 0 to n - 1 do
	rcu := conv_val CONV k (arg args1 i) (arg args2 i) !rcu
      done;
      !rcu
    else raise NotConvertible

let rec conv_eq pb t1 t2 cu =
  if t1 == t2 then cu 
  else
    match kind_of_term t1, kind_of_term t2 with
    | Rel n1, Rel n2 -> 
	if n1 = n2 then cu else raise NotConvertible
    | Meta m1, Meta m2 ->
	if m1 = m2 then cu else raise NotConvertible
    | Var id1, Var id2 -> 
	if id1 = id2 then cu else raise NotConvertible
    | Sort s1, Sort s2 -> sort_cmp pb s1 s2 cu
    | Cast (c1,_), _ -> conv_eq pb c1 t2 cu
    | _, Cast (c2,_) -> conv_eq pb t1 c2 cu
    | Prod (_,t1,c1), Prod (_,t2,c2) -> 
	conv_eq pb c1 c2 (conv_eq CONV t1 t2 cu)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) -> conv_eq CONV c1 c2 cu
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> 
	conv_eq pb c1 c2 (conv_eq CONV b1 b2 cu)
    | App (c1,l1), App (c2,l2) ->
	conv_eq_vect l1 l2 (conv_eq CONV c1 c2 cu)
    | Evar (e1,l1), Evar (e2,l2) ->
	if e1 = e2 then conv_eq_vect l1 l2 cu
	else raise NotConvertible
    | Const c1, Const c2 -> 
	if c1 = c2 then cu else raise NotConvertible
    | Ind c1, Ind c2 -> 
	if c1 = c2 then cu else raise NotConvertible
    | Construct c1, Construct c2 -> 
	if c1 = c2 then cu else raise NotConvertible
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
	let pcu = conv_eq CONV p1 p2 cu in
	let ccu = conv_eq CONV c1 c2 pcu in
	conv_eq_vect bl1 bl2 ccu
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
	if ln1 = ln2 then conv_eq_vect tl1 tl2 (conv_eq_vect bl1 bl2 cu)
	else raise NotConvertible
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->	
	if ln1 = ln2 then conv_eq_vect tl1 tl2 (conv_eq_vect bl1 bl2 cu)
	else raise NotConvertible
    | _ -> raise NotConvertible

and conv_eq_vect vt1 vt2 cu =
  let len = Array.length vt1 in
  if len = Array.length vt2 then
    let rcu = ref cu in
    for i = 0 to len-1 do
      rcu := conv_eq CONV vt1.(i) vt2.(i) !rcu
    done; !rcu
  else raise NotConvertible
      
let vconv pb env t1 t2 =
  let cu =
    try conv_eq pb t1 t2 Constraint.empty
    with NotConvertible ->
      infos := create_clos_infos betaiotazeta env;
      let v1 = val_of_constr env t1 in
      let v2 = val_of_constr env t2 in
      let cu = conv_val pb (nb_rel env) v1 v2 Constraint.empty in
      cu
  in cu
    
let use_vm = ref true
let _ = Reduction.set_vm_conv_cmp vconv
let set_use_vm b =
  use_vm := b;
  if b then Reduction.set_vm_conv_cmp vconv
  else Reduction.set_default_vm_conv ()
      
let use_vm _ = !use_vm

(*******************************************)
(* Calcul de la forme normal d'un terme    *)
(*******************************************)

let crazy_type = mkSet 

let decompose_prod env t =
  let (name,dom,codom as res) = destProd (whd_betadeltaiota env t) in
  if name = Anonymous then (Name (id_of_string "x"),dom,codom)
  else res

exception Find_at of int

(* rend le numero du constructeur correspondant au tag [tag],
   [cst] = true si c'est un constructeur constant *)

let invert_tag cst tag reloc_tbl =
  try 
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      if tag = tagj && (cst && arity = 0 || not(cst || arity = 0)) then
	raise (Find_at j)
      else ()
    done;raise Not_found 
  with Find_at j -> (j+1)   
             (* Argggg, ces constructeurs de ... qui commencent a 1*)

(* Build the substitution that replaces Rels by the appropriate 
  inductives *)
let ind_subst mind mib =
  let ntypes = mib.mind_ntypes in
  let make_Ik k = mkInd (mind,ntypes-k-1) in 
  Util.list_tabulate make_Ik ntypes

(* Instantiate inductives and parameters in constructor type
   in normal form *)
let constructor_instantiate mind mib params ctyp =
  let si = ind_subst mind mib in
  let ctyp1 = substl si ctyp in
  let nparams = Array.length params in
  if nparams = 0 then ctyp1
  else
    let _,ctyp2 = decompose_prod_n nparams ctyp1 in
    let sp = List.rev (Array.to_list params) in substl sp ctyp2
  
let destApplication t =
  try destApplication t 
  with _ -> t,[||]

let construct_of_constr_const env tag typ =
  let cind,params = destApplication (whd_betadeltaiota env typ) in
  let ind = destInd cind in
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  let rtbl = mip.mind_reloc_tbl in
  let i = invert_tag true tag rtbl in
  mkApp(mkConstruct(ind,i), params)

let find_rectype typ =
  let cind,args = destApplication typ in
  let ind = destInd cind in
  ind, args

let construct_of_constr_block env tag typ =
  let (mind,_ as ind),allargs = find_rectype (whd_betadeltaiota env typ) in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let nparams = mip.mind_nparams in
  let rtbl = mip.mind_reloc_tbl in
  let i = invert_tag false tag rtbl in
  let params = Array.sub allargs 0 nparams in
  let specif = mip.mind_nf_lc in
  let ctyp = constructor_instantiate mind mib params specif.(i-1) in
  (mkApp(mkConstruct(ind,i), params), ctyp)
  	
let constr_type_of_idkey env idkey =
  match idkey with
  | ConstKey cst ->
      let ty = (lookup_constant cst env).const_type in
      mkConst cst, ty
  | VarKey id -> 
      let (_,_,ty) = lookup_named id env in 
      mkVar id, ty
  | RelKey i -> 
      let n = (nb_rel env - i) in
      let (_,_,ty) = lookup_rel n env in
      mkRel n, lift n ty

let type_of_ind env ind = 
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_nf_arity

let build_branches_type (mind,_ as ind) mib mip params dep p rtbl =
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let build_one_branch i cty =
    let typi = constructor_instantiate mind mib params cty in
    let decl,indapp = Term.decompose_prod typi in
    let ind,cargs = find_rectype indapp in
    let nparams = Array.length params in
    let carity = snd (rtbl.(i)) in
    let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
    let codom = 
      let papp = mkApp(p,crealargs) in
      if dep then
	let cstr = ith_constructor_of_inductive ind (i+1) in
        let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
	let dep_cstr = mkApp(mkApp(mkConstruct cstr,params),relargs) in
	mkApp(papp,[|dep_cstr|])
      else papp
    in 
    decl, codom
  in Array.mapi build_one_branch mip.mind_nf_lc

(* La fonction de normalisation *)

let rec nf_val env v t = nf_whd env (whd_val v) t 

and nf_whd env whd typ =
  match whd with
  | Vsort s -> mkSort s
  | Vprod p ->
      let dom = nf_val env (dom p) crazy_type in
      let name = Name (id_of_string "x") in
      let vc = body_of_vfun (nb_rel env) (codom p) in
      let codom = nf_val (push_rel (name,None,dom) env) vc crazy_type in      
      mkProd(name,dom,codom)	  
  | Vfun f -> nf_fun env f typ
  | Vfix f -> nf_fix env f
  | Vfix_app fa ->
      let f = fix fa in
      let vargs = args_of_fix fa in
      let fd = nf_fix env f in
      let (_,i),(_,ta,_) = destFix fd in
      let t = ta.(i) in
      let _, args = nf_args  env vargs t in
      mkApp(fd,args)
  | Vcofix cf -> nf_cofix env cf 
  | Vcofix_app cfa -> 
      let cf = cofix cfa in
      let vargs = args_of_cofix cfa in
      let cfd = nf_cofix env cf in
      let i,(_,ta,_) = destCoFix cfd in
      let t = ta.(i) in
      let _, args = nf_args env vargs t in
      mkApp(cfd,args) 
  | Vconstr_const n -> construct_of_constr_const env n typ
  | Vconstr_block b ->
      let capp,ctyp = construct_of_constr_block env (btag b) typ in
      let args = nf_bargs env b ctyp in
      mkApp(capp,args)
  | Vatom_stk(Aid idkey, stk) ->
      let c,typ = constr_type_of_idkey env idkey in
      nf_stk env c typ stk
  | Vatom_stk(Aiddef(idkey,v), stk) ->
      nf_whd env (whd_stack v stk) typ
  | Vatom_stk(Aind ind, stk) ->
      nf_stk env (mkInd ind) (type_of_ind env ind) stk 
  | Vatom_stk(_,stk) -> assert false

and nf_stk env c t stk  =
  match stk with
  | [] -> c
  | Zapp vargs :: stk ->
      let t, args = nf_args env vargs t in
      nf_stk env (mkApp(c,args)) t stk 
  | Zfix fa :: stk ->   
      let f = fix fa in
      let vargs = args_of_fix fa in
      let fd = nf_fix env f in
      let (_,i),(_,ta,_) = destFix fd in
      let tf = ta.(i) in
      let typ, args = nf_args env vargs tf in
      let _,_,codom = decompose_prod env typ in
      nf_stk env (mkApp(mkApp(fd,args),[|c|])) (subst1 c codom) stk
  | Zswitch sw :: stk -> 
      let (mind,_ as ind),allargs = find_rectype (whd_betadeltaiota env t) in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let nparams = mip.mind_nparams in
      let params,realargs = Util.array_chop nparams allargs in
      (* calcul du predicat du case, 
        [dep] indique si c'est un case dependant *)
      let dep,p = 
	let dep = ref false in
	let rec nf_predicate env v pT =
	  match whd_val v, kind_of_term pT with
	  | Vfun f, Prod _ ->
	      let k = nb_rel env in
	      let vb = body_of_vfun k f in
	      let name,dom,codom = decompose_prod env pT in
	      let body = 
		nf_predicate (push_rel (name,None,dom) env) vb codom in
              mkLambda(name,dom,body)
	  | Vfun f, _ ->
	      dep := true;
	      let k = nb_rel env in
	      let vb = body_of_vfun k f in
	      let name = Name (id_of_string "c") in
	      let n = mip.mind_nrealargs in
	      let rargs = Array.init n (fun i -> mkRel (n-i)) in
	      let dom = mkApp(mkApp(mkInd ind,params),rargs) in
	      let body = 
		nf_val (push_rel (name,None,dom) env) vb crazy_type in
	      mkLambda(name,dom,body)
          | _, _ -> nf_val env v crazy_type
	in 
	let aux = nf_predicate env (type_of_switch sw) mip.mind_nf_arity in
	!dep,aux in
      (* Calcul du type des branches *)
      let btypes = 
	build_branches_type ind mib mip params dep p mip.mind_reloc_tbl in
      (* calcul des branches *)
      let bsw = branch_of_switch (nb_rel env) sw in
      let mkbranch i (n,v) =
	let decl,codom = btypes.(i) in
	let env = 
	  List.fold_right 
	    (fun (name,t) env -> push_rel (name,None,t) env) decl env in
	let b = nf_val env v codom in
	compose_lam decl b 
      in 
      let branchs = Array.mapi mkbranch bsw in
      let tcase = 
	if dep then mkApp(mkApp(p, params), [|c|])
	else mkApp(p, params)
      in
      let ci = case_info sw in
      nf_stk env (mkCase(ci, p, c, branchs)) tcase stk
       
and nf_args env vargs t =
  let t = ref t in
  let len = nargs vargs in
  let targs = 
    Array.init len 
      (fun i ->
	let _,dom,codom = decompose_prod env !t in
	let c = nf_val env (arg vargs i) dom in
	t := subst1 c codom; c) in
  !t,targs

and nf_bargs env b t =
  let t = ref t in
  let len = bsize b in
  let args = Array.create len crazy_type in
  for i = 0 to len - 1 do
    let _,dom,codom = decompose_prod env !t in
    let c = nf_val env (bfield b i) dom in
    args.(i) <- c;
    t := subst1 c codom
  done;
  args
(*  Array.init len 
    (fun i ->
      let _,dom,codom = decompose_prod env !t in
      let c = nf_val env (bfield b i) dom in
      t := subst1 c codom; c) *) 

and nf_fun env f typ =
  let k = nb_rel env in
  let vb = body_of_vfun k f in
  let name,dom,codom = decompose_prod env typ in
  let body = nf_val (push_rel (name,None,dom) env) vb codom in
  mkLambda(name,dom,body)

and nf_fix env f =
  let init = fix_init f in
  let rec_args = rec_args f in
  let ndef = fix_ndef f in
  let vt = types_of_fix f in
  let ft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (id_of_string "Ffix"))) in
  let k = nb_rel env in
  let vb = bodies_of_fix k f in 
  let env = push_rec_types (name,ft,ft) env in 
  let fb = Util.array_map2 (fun v t -> nf_fun env v t) vb ft in
  mkFix ((rec_args,init),(name,ft,fb))
  
and nf_cofix env cf =
  let init = cofix_init cf in
  let ndef = cofix_ndef cf in
  let vt = types_of_cofix cf in
  let cft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (id_of_string "Fcofix"))) in
  let k = nb_rel env in
  let vb = bodies_of_cofix k cf in 
  let env = push_rec_types (name,cft,cft) env in 
  let cfb = Util.array_map2 (fun v t -> nf_val env v t) vb cft in
  mkCoFix (init,(name,cft,cfb))
  


let cbv_vm env c t  =
  let transp = transp_values () in
  if not transp then set_transp_values true; 
  let v = val_of_constr env c in
  let c = nf_val env v t in
  if not transp then set_transp_values false; 
  c
  

