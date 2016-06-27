(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Declarations
open Term
open Vars
open Environ
open Inductive
open Reduction
open Vm
open Context.Rel.Declaration

(*******************************************)
(* Calcul de la forme normal d'un terme    *)
(*******************************************)

let crazy_type =  mkSet

let decompose_prod env t =
  let (name,dom,codom as res) = destProd (whd_betadeltaiota env t) in
  match name with
  | Anonymous -> (Name (Id.of_string "x"), dom, codom)
  | Name _ -> res

exception Find_at of int

(* rend le numero du constructeur correspondant au tag [tag],
   [cst] = true si c'est un constructeur constant *)

let invert_tag cst tag reloc_tbl =
  try
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      let no_arity = Int.equal arity 0 in
      if Int.equal tag tagj && (cst && no_arity || not (cst || no_arity)) then
	raise (Find_at j)
      else ()
    done;raise Not_found
  with Find_at j -> (j+1)
             (* Argggg, ces constructeurs de ... qui commencent a 1*)

let find_rectype_a env c = Inductiveops.find_mrectype_vect env Evd.empty c

(* Instantiate inductives and parameters in constructor type *)

let type_constructor mind mib u typ params =
  let s = ind_subst mind mib u in
  let ctyp = substl s typ in
  let ctyp = subst_instance_constr u ctyp in
  let ndecls = Context.Rel.length mib.mind_params_ctxt in
  if Int.equal ndecls 0 then ctyp
  else
    let _,ctyp = decompose_prod_n_assum ndecls ctyp in
    substl (List.rev (adjust_subst_to_rel_context mib.mind_params_ctxt (Array.to_list params)))
      ctyp



let construct_of_constr const env tag typ =
  let ((mind,_ as ind), u) as indu, allargs = find_rectype_a env typ in
  (* spiwack : here be a branch for specific decompilation handled by retroknowledge *)
  try
    if const then
      ((retroknowledge Retroknowledge.get_vm_decompile_constant_info env (mkIndU indu) tag),
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
    let ctyp = type_constructor mind mib u (mip.mind_nf_lc.(i-1)) params in
      (mkApp(mkConstructUi(indu,i), params), ctyp)

let construct_of_constr_const env tag typ =
  fst (construct_of_constr true env tag typ)

let construct_of_constr_block = construct_of_constr false

let type_of_ind env (ind, u) =
  type_of_inductive env (Inductive.lookup_mind_specif env ind, u)

let build_branches_type env (mind,_ as _ind) mib mip u params dep p =
  let rtbl = mip.mind_reloc_tbl in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let build_one_branch i cty =
    let typi = type_constructor mind mib u cty params in
    let decl,indapp = Reductionops.splay_prod env Evd.empty typi in
    let decl_with_letin,_ = decompose_prod_assum typi in
    let ((ind,u),cargs) = find_rectype_a env indapp in
    let nparams = Array.length params in
    let carity = snd (rtbl.(i)) in
    let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
    let codom =
      let ndecl = List.length decl in
      let papp = mkApp(lift ndecl p,crealargs) in
      if dep then
	let cstr = ith_constructor_of_inductive ind (i+1) in
        let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
	let params = Array.map (lift ndecl) params in
	let dep_cstr = mkApp(mkApp(mkConstructU (cstr,u),params),relargs) in
	mkApp(papp,[|dep_cstr|])
      else papp
    in
    decl, decl_with_letin, codom
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
      let name = Name (Id.of_string "x") in
      let vc = body_of_vfun (nb_rel env) (codom p) in
      let codom = nf_vtype (push_rel (LocalAssum (name,dom)) env) vc  in
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
  | Vconstr_const n ->
    construct_of_constr_const env n typ
  | Vconstr_block b ->
      let tag = btag b in
      let (tag,ofs) =
        if tag = Cbytecodes.last_variant_tag then
	  match whd_val (bfield b 0) with
	  | Vconstr_const tag -> (tag+Cbytecodes.last_variant_tag, 1)
	  | _ -> assert false
        else (tag, 0) in
      let capp,ctyp = construct_of_constr_block env tag typ in
      let args = nf_bargs env b ofs ctyp in
      mkApp(capp,args)
  | Vatom_stk(Aid idkey, stk) ->
      constr_type_of_idkey env idkey stk
  | Vatom_stk(Aind ((mi,i) as ind), stk) ->
     let mib = Environ.lookup_mind mi env in
     let nb_univs =
       if mib.mind_polymorphic then Univ.UContext.size mib.mind_universes
       else 0
     in
     let mk u =
       let pind = (ind, u) in (mkIndU pind, type_of_ind env pind)
     in
     nf_univ_args ~nb_univs mk env stk
  | Vatom_stk(Atype u, stk) -> assert false
  | Vuniv_level lvl ->
    assert false

and nf_univ_args ~nb_univs mk env stk =
  let u =
    if Int.equal nb_univs 0 then Univ.Instance.empty
    else match stk with
    | Zapp args :: _ ->
       let inst =
	 Array.init nb_univs (fun i -> Vm.uni_lvl_val (arg args i))
       in
       Univ.Instance.of_array inst
    | _ -> assert false
  in
  let (t,ty) = mk u in
  nf_stk ~from:nb_univs env t ty stk

and constr_type_of_idkey env (idkey : Vars.id_key) stk =
  match idkey with
  | ConstKey cst ->
     let cbody = Environ.lookup_constant cst env in
     let nb_univs =
       if cbody.const_polymorphic then Univ.UContext.size cbody.const_universes
       else 0
     in
     let mk u =
       let pcst = (cst, u) in (mkConstU pcst, Typeops.type_of_constant_in env pcst)
     in
     nf_univ_args ~nb_univs mk env stk
   | VarKey id ->
      let open Context.Named.Declaration in
      let ty = get_type (lookup_named id env) in
      nf_stk env (mkVar id) ty stk
  | RelKey i ->
      let n = (nb_rel env - i) in
      let ty = get_type (lookup_rel n env) in
      nf_stk env (mkRel n) (lift n ty) stk

and nf_stk ?from:(from=0) env c t stk  =
  match stk with
  | [] -> c
  | Zapp vargs :: stk ->
      if nargs vargs >= from then
	let t, args = nf_args ~from:from env vargs t in
	nf_stk env (mkApp(c,args)) t stk
      else
	let rest = from - nargs vargs in
	nf_stk ~from:rest env c t stk
  | Zfix (f,vargs) :: stk ->
      assert (from = 0) ;
      let fa, typ = nf_fix_app env f vargs in
      let _,_,codom = decompose_prod env typ in
      nf_stk env (mkApp(fa,[|c|])) (subst1 c codom) stk
  | Zswitch sw :: stk ->
      assert (from = 0) ;
      let ((mind,_ as ind), u), allargs = find_rectype_a env t in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params,realargs = Util.Array.chop nparams allargs in
      let pT =
	hnf_prod_applist env (type_of_ind env (ind,u)) (Array.to_list params) in
      let pT = whd_betadeltaiota env pT in
      let dep, p = nf_predicate env (ind,u) mip params (type_of_switch sw) pT in
      (* Calcul du type des branches *)
      let btypes = build_branches_type env ind mib mip u params dep p in
      (* calcul des branches *)
      let bsw = branch_of_switch (nb_rel env) sw in
      let mkbranch i (n,v) =
	let decl,decl_with_letin,codom = btypes.(i) in
	let b = nf_val (Termops.push_rels_assum decl env) v codom in
        Termops.it_mkLambda_or_LetIn_from_no_LetIn b decl_with_letin
      in
      let branchs = Array.mapi mkbranch bsw in
      let tcase = build_case_type dep p realargs c in
      let ci = case_info sw in
      nf_stk env (mkCase(ci, p, c, branchs)) tcase stk
  | Zproj p :: stk ->
     assert (from = 0) ;
     let p' = Projection.make p true in
     let ty = Inductiveops.type_of_projection_knowing_arg env Evd.empty p' c t in
     nf_stk env (mkProj(p',c)) ty stk

and nf_predicate env ind mip params v pT =
  match whd_val v, kind_of_term pT with
  | Vfun f, Prod _ ->
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name,dom,codom = decompose_prod env pT in
      let dep,body =
	nf_predicate (push_rel (LocalAssum (name,dom)) env) ind mip params vb codom in
      dep, mkLambda(name,dom,body)
  | Vfun f, _ ->
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name = Name (Id.of_string "c") in
      let n = mip.mind_nrealargs in
      let rargs = Array.init n (fun i -> mkRel (n-i)) in
      let params = if Int.equal n 0 then params else Array.map (lift n) params in
      let dom = mkApp(mkIndU ind,Array.append params rargs) in
      let body = nf_vtype (push_rel (LocalAssum (name,dom)) env) vb in
      true, mkLambda(name,dom,body)
  | _, _ -> false, nf_val env v crazy_type

and nf_args env vargs ?from:(f=0) t =
  let t = ref t in
  let len = nargs vargs - f in
  let args =
    Array.init len
      (fun i ->
	let _,dom,codom = decompose_prod env !t in
	let c = nf_val env (arg vargs (f+i)) dom in
	t := subst1 c codom; c) in
  !t,args

and nf_bargs env b ofs t =
  let t = ref t in
  let len = bsize b - ofs in
  let args =
    Array.init len
      (fun i ->
	let _,dom,codom = decompose_prod env !t in
	let c = nf_val env (bfield b (i+ofs)) dom in
	t := subst1 c codom; c) in
  args

and nf_fun env f typ =
  let k = nb_rel env in
  let vb = body_of_vfun k f in
  let name,dom,codom =
    try decompose_prod env typ
    with DestKO ->
      (* 27/2/13: Turned this into an anomaly *)
      CErrors.anomaly
        (Pp.strbrk "Returned a functional value in a type not recognized as a product type.")
  in
  let body = nf_val (push_rel (LocalAssum (name,dom)) env) vb codom in
  mkLambda(name,dom,body)

and nf_fix env f =
  let init = current_fix f in
  let rec_args = rec_args f in
  let k = nb_rel env in
  let vb, vt = reduce_fix k f in
  let ndef = Array.length vt in
  let ft = Array.map (fun v -> nf_val env v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (Id.of_string "Ffix"))) in
  (* Third argument of the tuple is ignored by push_rec_types *)
  let env = push_rec_types (name,ft,ft) env in
  (* We lift here because the types of arguments (in tt) will be evaluated
     in an environment where the fixpoints have been pushed *)
  let norm_vb v t = nf_fun env v (lift ndef t) in
  let fb = Util.Array.map2 norm_vb vb ft in
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
  let name = Array.init ndef (fun _ -> (Name (Id.of_string "Fcofix"))) in
  let env = push_rec_types (name,cft,cft) env in
  let cfb = Util.Array.map2 (fun v t -> nf_val env v t) vb cft in
  mkCoFix (init,(name,cft,cfb))

let cbv_vm env c t  =
  let v = Vconv.val_of_constr env c in
  nf_val env v t

let vm_infer_conv ?(pb=Reduction.CUMUL) env sigma t1 t2 =
  Reductionops.infer_conv_gen (fun pb ~l2r sigma ts -> Vconv.vm_conv_gen pb)
    ~catch_incon:true ~pb env sigma t1 t2

let _ = Reductionops.set_vm_infer_conv vm_infer_conv
