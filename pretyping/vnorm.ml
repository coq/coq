(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Declarations
open Term
open Constr
open Vars
open Environ
open Inductive
open Reduction
open Vmvalues
open Vm
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(*******************************************)
(* Calcul de la forme normal d'un terme    *)
(*******************************************)

let crazy_type =  mkSet

let decompose_prod env t =
  let (name,dom,codom as res) = destProd (whd_all env t) in
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

let find_rectype_a env c =
  let (t, l) = decompose_appvect (whd_all env c) in
  match kind t with
  | Ind ind -> (ind, l)
  | _ -> assert false

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
      ((Retroknowledge.get_vm_decompile_constant_info env.retroknowledge (mkIndU indu) tag),
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

let build_branches_type env sigma (mind,_ as _ind) mib mip u params p =
  let rtbl = mip.mind_reloc_tbl in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let build_one_branch i cty =
    let typi = type_constructor mind mib u cty params in
    let decl,indapp = Reductionops.splay_prod env sigma (EConstr.of_constr typi) in
    let decl = List.map (on_snd EConstr.Unsafe.to_constr) decl in
    let indapp = EConstr.Unsafe.to_constr indapp in
    let decl_with_letin,_ = decompose_prod_assum typi in
    let ((ind,u),cargs) = find_rectype_a env indapp in
    let nparams = Array.length params in
    let carity = snd (rtbl.(i)) in
    let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
    let codom =
      let ndecl = List.length decl in
      let papp = mkApp(lift ndecl p,crealargs) in
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
      let params = Array.map (lift ndecl) params in
      let dep_cstr = mkApp(mkApp(mkConstructU (cstr,u),params),relargs) in
      mkApp(papp,[|dep_cstr|])
    in
    decl, decl_with_letin, codom
  in Array.mapi build_one_branch mip.mind_nf_lc

let build_case_type p realargs c =
  mkApp(mkApp(p, realargs), [|c|])

(* La fonction de normalisation *)

let rec nf_val env sigma v t = nf_whd env sigma (Vmvalues.whd_val v) t

and nf_vtype env sigma v =  nf_val env sigma v crazy_type

and nf_whd env sigma whd typ =
  match whd with
  | Vprod p ->
      let dom = nf_vtype env sigma (dom p) in
      let name = Name (Id.of_string "x") in
      let vc = reduce_fun (nb_rel env) (codom p) in
      let codom = nf_vtype (push_rel (LocalAssum (name,dom)) env) sigma vc  in
      mkProd(name,dom,codom)
  | Vfun f -> nf_fun env sigma f typ
  | Vfix(f,None) -> nf_fix env sigma f
  | Vfix(f,Some vargs) -> fst (nf_fix_app env sigma f vargs)
  | Vcofix(cf,_,None) -> nf_cofix env sigma cf
  | Vcofix(cf,_,Some vargs) ->
      let cfd = nf_cofix env sigma cf in
      let i,(_,ta,_) = destCoFix cfd in
      let t = ta.(i) in
      let _, args = nf_args env sigma vargs t in
      mkApp(cfd,args)
  | Vconstr_const n ->
    construct_of_constr_const env n typ
  | Vconstr_block b ->
      let tag = btag b in
      let (tag,ofs) =
        if tag = Obj.last_non_constant_constructor_tag then
	  match whd_val (bfield b 0) with
          | Vconstr_const tag -> (tag+Obj.last_non_constant_constructor_tag, 1)
	  | _ -> assert false
        else (tag, 0) in
      let capp,ctyp = construct_of_constr_block env tag typ in
      let args = nf_bargs env sigma b ofs ctyp in
      mkApp(capp,args)
  | Vatom_stk(Aid idkey, stk) ->
      constr_type_of_idkey env sigma idkey stk
  | Vatom_stk(Aind ((mi,i) as ind), stk) ->
     let mib = Environ.lookup_mind mi env in
     let nb_univs =
       Univ.AUContext.size (Declareops.inductive_polymorphic_context mib)
     in
     let mk u =
       let pind = (ind, u) in (mkIndU pind, type_of_ind env pind)
     in
     nf_univ_args ~nb_univs mk env sigma stk
  | Vatom_stk(Asort s, stk) ->
    assert (List.is_empty stk); mkSort s
  | Vuniv_level lvl ->
    assert false

and nf_univ_args ~nb_univs mk env sigma stk =
  let u =
    if Int.equal nb_univs 0 then Univ.Instance.empty
    else match stk with
    | Zapp args :: _ ->
       let inst =
         Array.init nb_univs (fun i -> uni_lvl_val (arg args i))
       in
       Univ.Instance.of_array inst
    | _ -> assert false
  in
  let (t,ty) = mk u in
  nf_stk ~from:nb_univs env sigma t ty stk

and nf_evar env sigma evk stk =
  let evi = try Evd.find sigma evk with Not_found -> assert false in
  let hyps = Environ.named_context_of_val (Evd.evar_filtered_hyps evi) in
  let concl = EConstr.Unsafe.to_constr @@ Evd.evar_concl evi in
  if List.is_empty hyps then
    nf_stk env sigma (mkEvar (evk, [||])) concl stk
  else match stk with
  | Zapp args :: stk ->
    (** We assume that there is no consecutive Zapp nodes in a VM stack. Is that
        really an invariant? *)
    (** Let-bound arguments are present in the evar arguments but not in the
        type, so we turn the let into a product. *)
    let hyps = Context.Named.drop_bodies hyps in
    let fold accu d = Term.mkNamedProd_or_LetIn d accu in
    let t = List.fold_left fold concl hyps in
    let t, args = nf_args env sigma args t in
    let inst, args = Array.chop (List.length hyps) args in
    let c = mkApp (mkEvar (evk, inst), args) in
    nf_stk env sigma c t stk
  | _ ->
    CErrors.anomaly (Pp.str "Argument size mismatch when decompiling an evar")

and constr_type_of_idkey env sigma (idkey : Vmvalues.id_key) stk =
  match idkey with
  | ConstKey cst ->
     let cbody = Environ.lookup_constant cst env in
     let nb_univs =
       Univ.AUContext.size (Declareops.constant_polymorphic_context cbody)
     in
     let mk u =
       let pcst = (cst, u) in (mkConstU pcst, Typeops.type_of_constant_in env pcst)
     in
     nf_univ_args ~nb_univs mk env sigma stk
   | VarKey id ->
      let ty = NamedDecl.get_type (lookup_named id env) in
      nf_stk env sigma (mkVar id) ty stk
  | RelKey i ->
      let n = (nb_rel env - i) in
      let ty = RelDecl.get_type (lookup_rel n env) in
      nf_stk env sigma (mkRel n) (lift n ty) stk
  | EvarKey evk ->
      nf_evar env sigma evk stk

and nf_stk ?from:(from=0) env sigma c t stk  =
  match stk with
  | [] -> c
  | Zapp vargs :: stk ->
      if nargs vargs >= from then
	let t, args = nf_args ~from:from env sigma vargs t in
	nf_stk env sigma (mkApp(c,args)) t stk
      else
	let rest = from - nargs vargs in
	nf_stk ~from:rest env sigma c t stk
  | Zfix (f,vargs) :: stk ->
      assert (from = 0) ;
      let fa, typ = nf_fix_app env sigma f vargs in
      let _,_,codom = decompose_prod env typ in
      nf_stk env sigma (mkApp(fa,[|c|])) (subst1 c codom) stk
  | Zswitch sw :: stk ->
      assert (from = 0) ;
      let ((mind,_ as ind), u), allargs = find_rectype_a env t in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params,realargs = Util.Array.chop nparams allargs in
      let nparamdecls = Context.Rel.length (Inductive.inductive_paramdecls (mib,u)) in
      let pT =
        hnf_prod_applist_assum env nparamdecls (type_of_ind env (ind,u)) (Array.to_list params) in
      let p = nf_predicate env sigma (ind,u) mip params (type_of_switch sw) pT in
      (* Calcul du type des branches *)
      let btypes = build_branches_type env sigma ind mib mip u params p in
      (* calcul des branches *)
      let bsw = branch_of_switch (nb_rel env) sw in
      let mkbranch i (n,v) =
	let decl,decl_with_letin,codom = btypes.(i) in
	let b = nf_val (Termops.push_rels_assum decl env) sigma v codom in
        Termops.it_mkLambda_or_LetIn_from_no_LetIn b decl_with_letin
      in
      let branchs = Array.mapi mkbranch bsw in
      let tcase = build_case_type p realargs c in
      let ci = sw.sw_annot.Vmvalues.ci in
      nf_stk env sigma (mkCase(ci, p, c, branchs)) tcase stk
  | Zproj p :: stk ->
     assert (from = 0) ;
     let p' = Projection.make p true in
     let ty = Inductiveops.type_of_projection_knowing_arg env sigma p' (EConstr.of_constr c) (EConstr.of_constr t) in
     nf_stk env sigma (mkProj(p',c)) ty stk

and nf_predicate env sigma ind mip params v pT =
  match kind (whd_allnolet env pT) with
  | LetIn (name,b,t,pT) ->
      let body =
        nf_predicate (push_rel (LocalDef (name,b,t)) env) sigma ind mip params v pT in
      mkLetIn (name,b,t,body)
  | Prod (name,dom,codom) -> begin
    match whd_val v with
    | Vfun f ->
      let k = nb_rel env in
      let vb = reduce_fun k f in
      let body =
	nf_predicate (push_rel (LocalAssum (name,dom)) env) sigma ind mip params vb codom in
      mkLambda(name,dom,body)
    | _ -> assert false
    end
  | _ ->
    match whd_val v with
    | Vfun f ->
      let k = nb_rel env in
      let vb = reduce_fun k f in
      let name = Name (Id.of_string "c") in
      let n = mip.mind_nrealargs in
      let rargs = Array.init n (fun i -> mkRel (n-i)) in
      let params = if Int.equal n 0 then params else Array.map (lift n) params in
      let dom = mkApp(mkIndU ind,Array.append params rargs) in
      let body = nf_vtype (push_rel (LocalAssum (name,dom)) env) sigma vb in
      mkLambda(name,dom,body)
    | _ -> assert false

and nf_args env sigma vargs ?from:(f=0) t =
  let t = ref t in
  let len = nargs vargs - f in
  let args =
    Array.init len
      (fun i ->
	let _,dom,codom = decompose_prod env !t in
	let c = nf_val env sigma (arg vargs (f+i)) dom in
	t := subst1 c codom; c) in
  !t,args

and nf_bargs env sigma b ofs t =
  let t = ref t in
  let len = bsize b - ofs in
  let args =
    Array.init len
      (fun i ->
	let _,dom,codom = decompose_prod env !t in
	let c = nf_val env sigma (bfield b (i+ofs)) dom in
	t := subst1 c codom; c) in
  args

and nf_fun env sigma f typ =
  let k = nb_rel env in
  let vb = reduce_fun k f in
  let name,dom,codom =
    try decompose_prod env typ
    with DestKO ->
      (* 27/2/13: Turned this into an anomaly *)
      CErrors.anomaly
        (Pp.strbrk "Returned a functional value in a type not recognized as a product type.")
  in
  let body = nf_val (push_rel (LocalAssum (name,dom)) env) sigma vb codom in
  mkLambda(name,dom,body)

and nf_fix env sigma f =
  let init = current_fix f in
  let rec_args = rec_args f in
  let k = nb_rel env in
  let vb, vt = reduce_fix k f in
  let ndef = Array.length vt in
  let ft = Array.map (fun v -> nf_val env sigma v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (Id.of_string "Ffix"))) in
  (* Third argument of the tuple is ignored by push_rec_types *)
  let env = push_rec_types (name,ft,ft) env in
  (* We lift here because the types of arguments (in tt) will be evaluated
     in an environment where the fixpoints have been pushed *)
  let norm_vb v t = nf_fun env sigma v (lift ndef t) in
  let fb = Util.Array.map2 norm_vb vb ft in
  mkFix ((rec_args,init),(name,ft,fb))

and nf_fix_app env sigma f vargs =
  let fd = nf_fix env sigma f in
  let (_,i),(_,ta,_) = destFix fd in
  let t = ta.(i) in
  let t, args = nf_args env sigma vargs t in
  mkApp(fd,args),t

and nf_cofix env sigma cf =
  let init = current_cofix cf in
  let k = nb_rel env in
  let vb,vt = reduce_cofix k cf in
  let ndef = Array.length vt in
  let cft = Array.map (fun v -> nf_val env sigma v crazy_type) vt in
  let name = Array.init ndef (fun _ -> (Name (Id.of_string "Fcofix"))) in
  let env = push_rec_types (name,cft,cft) env in
  let cfb = Util.Array.map2 (fun v t -> nf_val env sigma v t) vb cft in
  mkCoFix (init,(name,cft,cfb))

let cbv_vm env sigma c t  =
  if Termops.occur_meta sigma c then
    CErrors.user_err Pp.(str "vm_compute does not support metas.");
  (** This evar-normalizes terms beforehand *)
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let t = EConstr.to_constr ~abort_on_undefined_evars:false sigma t in
  let v = Csymtable.val_of_constr env c in
  EConstr.of_constr (nf_val env sigma v t)

let vm_infer_conv ?(pb=Reduction.CUMUL) env sigma t1 t2 =
  Reductionops.infer_conv_gen (fun pb ~l2r sigma ts -> Vconv.vm_conv_gen pb)
    ~catch_incon:true ~pb env sigma t1 t2

let _ = if Coq_config.bytecode_compiler then Reductionops.set_vm_infer_conv vm_infer_conv
