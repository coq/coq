(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Declarations
open Term
open Environ
open Inductive
open Reduction
open Vm

(*******************************************)
(* Calcul de la forme normal d'un terme    *)
(*******************************************)

let crazy_type =  mkSet

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

let find_rectype_a env c =
  let (t, l) =
    let t = whd_betadeltaiota env c in
    try destApp t with _ -> (t,[||]) in
  match kind_of_term t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

(* Instantiate inductives and parameters in constructor type *)

let type_constructor mind mib typ params =
  let s = ind_subst mind mib in
  let ctyp = substl s typ in
  let nparams = Array.length params in
  if nparams = 0 then ctyp
  else
    let _,ctyp = decompose_prod_n nparams ctyp in
    substl (List.rev (Array.to_list params)) ctyp



let construct_of_constr const env tag typ =
  let (mind,_ as ind), allargs = find_rectype_a env typ in
  (* spiwack : here be a branch for specific decompilation handled by retroknowledge *)
  try
    if const then
      ((retroknowledge Retroknowledge.get_vm_decompile_constant_info env (Ind ind) tag),
       typ) (*spiwack: this may need to be changed in case there are parameters in the
	               type which may cause a constant value to have an arity.
	               (type_constructor seems to be all about parameters actually)
	               but it shouldn't really matter since constant values don't use
	               their ctyp in the rest of the code.*)
    else
      raise Not_found (* No retroknowledge function (yet) for block decompilation *)
  with Not_found ->
    let mib,mip = lookup_mind_specif env ind in
    let nparams = mib.mind_nparams in
    let i = invert_tag const tag mip.mind_reloc_tbl in
    let params = Array.sub allargs 0 nparams in
    let ctyp = type_constructor mind mib (mip.mind_nf_lc.(i-1)) params in
      (mkApp(mkConstruct(ind,i), params), ctyp)

let construct_of_constr_const env tag typ =
  fst (construct_of_constr true env tag typ)

let construct_of_constr_block = construct_of_constr false

let constr_type_of_idkey env idkey =
  match idkey with
  | ConstKey cst ->
      mkConst cst, Typeops.type_of_constant env cst
  | VarKey id ->
      let (_,_,ty) = lookup_named id env in
      mkVar id, ty
  | RelKey i ->
      let n = (nb_rel env - i) in
      let (_,_,ty) = lookup_rel n env in
      mkRel n, lift n ty

let type_of_ind env ind =
  type_of_inductive env (Inductive.lookup_mind_specif env ind)

let build_branches_type env (mind,_ as _ind) mib mip params dep p =
  let rtbl = mip.mind_reloc_tbl in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let build_one_branch i cty =
    let typi = type_constructor mind mib cty params in
    let decl,indapp = Term.decompose_prod typi in
    let ind,cargs = find_rectype_a env indapp in
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

let build_case_type dep p realargs c =
  if dep then mkApp(mkApp(p, realargs), [|c|])
  else mkApp(p, realargs)

(* La fonction de normalisation *)

let rec nf_val env v t = nf_whd env (whd_val v) t

and nf_vtype env v =  nf_val env v crazy_type

and nf_whd env whd typ =
  match whd with
  | Vsort s -> mkSort s
  | Vprod p ->
      let dom = nf_vtype env (dom p) in
      let name = Name (id_of_string "x") in
      let vc = body_of_vfun (nb_rel env) (codom p) in
      let codom = nf_vtype (push_rel (name,None,dom) env) vc  in
      mkProd(name,dom,codom)
  | Vfun f -> nf_fun env f typ
  | Vfix(f,None) -> nf_fix env f
  | Vfix(f,Some vargs) -> fst (nf_fix_app env f vargs)
  | Vcofix(cf,_,None) -> nf_cofix env cf
  | Vcofix(cf,_,Some vargs) ->
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

and nf_stk env c t stk  =
  match stk with
  | [] -> c
  | Zapp vargs :: stk ->
      let t, args = nf_args env vargs t in
      nf_stk env (mkApp(c,args)) t stk
  | Zfix (f,vargs) :: stk ->
      let fa, typ = nf_fix_app env f vargs in
      let _,_,codom = try decompose_prod env typ with _ -> exit 120 in
      nf_stk env (mkApp(fa,[|c|])) (subst1 c codom) stk
  | Zswitch sw :: stk ->
      let (mind,_ as ind),allargs = find_rectype_a env t in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params,realargs = Util.array_chop nparams allargs in
      let pT =
	hnf_prod_applist env (type_of_ind env ind) (Array.to_list params) in
      let pT = whd_betadeltaiota env pT in
      let dep, p = nf_predicate env ind mip params (type_of_switch sw) pT in
      (* Calcul du type des branches *)
      let btypes = build_branches_type env ind mib mip params dep p in
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
      let tcase = build_case_type dep p realargs c in
      let ci = case_info sw in
      nf_stk env (mkCase(ci, p, c, branchs)) tcase stk

and nf_predicate env ind mip params v pT =
  match whd_val v, kind_of_term pT with
  | Vfun f, Prod _ ->
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name,dom,codom = try decompose_prod env pT with _ -> exit 121 in
      let dep,body =
	nf_predicate (push_rel (name,None,dom) env) ind mip params vb codom in
      dep, mkLambda(name,dom,body)
  | Vfun f, _ ->
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name = Name (id_of_string "c") in
      let n = mip.mind_nrealargs in
      let rargs = Array.init n (fun i -> mkRel (n-i)) in
      let params = if n=0 then params else Array.map (lift n) params in
      let dom = mkApp(mkInd ind,Array.append params rargs) in
      let body = nf_vtype (push_rel (name,None,dom) env) vb in
      true, mkLambda(name,dom,body)
  | _, _ -> false, nf_val env v crazy_type

and nf_args env vargs t =
  let t = ref t in
  let len = nargs vargs in
  let args =
    Array.init len
      (fun i ->
	let _,dom,codom = try decompose_prod env !t with _ -> exit 123 in
	let c = nf_val env (arg vargs i) dom in
	t := subst1 c codom; c) in
  !t,args

and nf_bargs env b t =
  let t = ref t in
  let len = bsize b in
  let args =
    Array.init len
      (fun i ->
	let _,dom,codom = try decompose_prod env !t with _ -> exit 124 in
	let c = nf_val env (bfield b i) dom in
	t := subst1 c codom; c) in
  args

and nf_fun env f typ =
  let k = nb_rel env in
  let vb = body_of_vfun k f in
  let name,dom,codom =
    try decompose_prod env typ
    with _ ->
      raise (Type_errors.TypeError(env,Type_errors.ReferenceVariables typ))
  in
  let body = nf_val (push_rel (name,None,dom) env) vb codom in
  mkLambda(name,dom,body)

and nf_fix env f =
  let init = current_fix f in
  let rec_args = rec_args f in
  let k = nb_rel env in
  let vb, vt = reduce_fix k f in
  let ndef = Array.length vt in
  let ft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (id_of_string "Ffix"))) in
  let env = push_rec_types (name,ft,ft) env in
  let fb = Util.array_map2 (fun v t -> nf_fun env v t) vb ft in
  mkFix ((rec_args,init),(name,ft,fb))

and nf_fix_app env f vargs =
  let fd = nf_fix env f in
  let (_,i),(_,ta,_) = destFix fd in
  let t = ta.(i) in
  let t, args = nf_args env vargs t in
  mkApp(fd,args),t

and nf_cofix env cf =
  let init = current_cofix cf in
  let k = nb_rel env in
  let vb,vt = reduce_cofix k cf in
  let ndef = Array.length vt in
  let cft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (id_of_string "Fcofix"))) in
  let env = push_rec_types (name,cft,cft) env in
  let cfb = Util.array_map2 (fun v t -> nf_val env v t) vb cft in
  mkCoFix (init,(name,cft,cfb))

let cbv_vm env c t  =
  let transp = transp_values () in
  if not transp then set_transp_values true;
  let v = Vconv.val_of_constr env c in
  let c = nf_val env v t in
  if not transp then set_transp_values false;
  c

