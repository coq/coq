(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

let find_rectype_a env c =
  let (t, l) =
    let t = whd_betadeltaiota env c in
    try destApp t with DestKO -> (t,[||]) in
  match kind_of_term t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

(* Instantiate inductives and parameters in constructor type *)

let type_constructor mind mib u typ params =
  let s = ind_subst mind mib u in
  let ctyp = substl s typ in
  let ctyp = subst_instance_constr u ctyp in
  let nparams = Array.length params in
  if Int.equal nparams 0 then ctyp
  else
    let _,ctyp = decompose_prod_n nparams ctyp in
    substl (Array.rev_to_list params) ctyp



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

(** TODO: This should almost certainly go somewhere else *)
let get_universe_level : values -> Univ.universe_level =
  fun v ->
    match Obj.magic v with
    | Vuniv_level lvl ->
      Pp.(msg_debug (str "lvl = " ++ Univ.Level.pr lvl)) ;
      lvl
    | Vsort s -> assert false
    | Vprod s -> assert false
    | Vfun _ -> assert false
    | Vfix _ -> assert false
    | Vcofix _ -> assert false
    | Vconstr_const _ -> assert false
    | Vconstr_block _ -> assert false
    | Vatom_stk _ -> assert false

let parse_universe_instance (ui : Term.values) : Univ.Instance.t =
  match whd_val ui with
  | Vconstr_block blk ->
    Printf.fprintf stderr "tag = %d ; size = %d\n" (btag blk) (bsize blk) ;
    assert (btag blk = Cbytecodes.univ_instance_tag) ;
    (* parse this as a universe *)
    let inst = Univ.Instance.of_array
      (Array.init (bsize blk)
	 (fun i ->
	   Printf.fprintf stderr "i = %d\n" i ;
	   get_universe_level (bfield blk i)))
    in
    Pp.(msg_debug (str "parsed universe levels = " ++
		     Univ.Instance.pr Univ.Level.pr inst)) ;
    inst
  | _ ->
    Printf.fprintf stderr "not a block\n" ;
    assert false

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
  | Vconstr_const n ->
    construct_of_constr_const env n typ
  | Vconstr_block b ->
      Printf.fprintf stderr "Vconstr_block\n" ;
      let tag = btag b in
      Printf.fprintf stderr "tag = %d\n" tag ;
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
      constr_type_of_idkey env idkey stk nf_stk
  | Vatom_stk(Aiddef(idkey,v), stk) ->
      nf_whd env (whd_stack v stk) typ
  | Vatom_stk(Aind ((mi,i) as ind), stk) ->
      if Environ.polymorphic_ind ind env then
	let mib = Environ.lookup_mind mi env in
	let ulen = Univ.UContext.size mib.mind_universes in
	match stk with
	| Zapp args :: stk' ->
	  assert (ulen <= nargs args) ;
	  let inst =
	    Array.init ulen (fun i -> get_universe_level (arg args i))
	  in
	  let pind = (ind, Univ.Instance.of_array inst) in
	  nf_stk ~from:ulen env (mkIndU pind) (type_of_ind env pind) stk
	| _ -> assert false
      else
	let pind = (ind, Univ.Instance.empty) in
	nf_stk env (mkIndU pind) (type_of_ind env pind) stk
  | Vatom_stk(Atype u, stk) ->
    begin
      match stk with
      | [Zapp args] ->
	Printf.eprintf "running here! univ = \n" ; flush stderr ;
	Pp.(msg_debug (Univ.pr_uni u)) ;
	flush stderr ; flush stdout ;
	assert (Univ.LSet.cardinal (Univ.Universe.levels u) = nargs args) ;
	let _,mp = Univ.LSet.fold (fun key (i,mp) ->
	  Printf.eprintf "getting %d\n" i ; flush stderr ;
	  Printf.eprintf "tag = %d\n" (Obj.tag (Obj.repr (arg args i))) ; flush stderr ;
	  let u = get_universe_level (arg args i) in
	  (i+1, Univ.LMap.add key (Univ.Universe.make u) mp))
	  (Univ.Universe.levels u)
	  (0,Univ.LMap.empty) in
	Printf.eprintf "finished map\n" ; flush stderr ;
	let subst = Univ.make_subst mp in
	Printf.eprintf "made subst\n" ; flush stderr ;
	let nuniv = Univ.subst_univs_universe subst u in
	Printf.eprintf "substituted\n" ; flush stderr ;
	mkSort (Type nuniv)
      | _ -> assert false
    end
  | Vuniv_level lvl ->
    assert false

and constr_type_of_idkey env (idkey : Vars.id_key) stk cont =
  match idkey with
  | ConstKey cst ->
    if Environ.polymorphic_constant cst env then
      match stk with
      | Zapp vargs :: stk' when Vm.nargs vargs = 1 ->
	let ui = parse_universe_instance (Vm.arg vargs 0) in
	let ucst = (cst, ui) in
	let const_type = Typeops.type_of_constant_in env ucst in
	cont env (mkConstU ucst) const_type stk'
      | Zapp vargs :: stk' when Vm.nargs vargs > 1 ->
	let ui = parse_universe_instance (Vm.arg vargs 0) in
	let ucst = (cst, ui) in
	let const_type = Typeops.type_of_constant_in env ucst in
	let t, args = nf_args env vargs ~from:1 const_type in
	cont env (mkApp (mkConstU ucst, args)) t stk'
      | _ -> assert false
    else
      begin
	let ucst = (cst, Univ.Instance.empty) in
	let const_type = Typeops.type_of_constant_in env ucst in
	(* Even if the constant is not universe polymorphic,
         * it still gets a universe. That instance is just empty.
	 *)
	match stk with
	| Zapp vargs :: stk' ->
	  if Vm.nargs vargs = 1 then
	    cont env (mkConstU ucst) const_type stk'
	  else if Vm.nargs vargs > 1 then
	    let t, args = nf_args env vargs ~from:1 const_type in
	    cont env (mkApp (mkConstU ucst, args)) t stk'
	  else
	    assert false
	| _ -> assert false
      end
  | VarKey id ->
      let (_,_,ty) = lookup_named id env in
      cont env (mkVar id) ty stk
  | RelKey i ->
      let n = (nb_rel env - i) in
      let (_,_,ty) = lookup_rel n env in
      cont env (mkRel n) (lift n ty) stk

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
	nf_predicate (push_rel (name,None,dom) env) ind mip params vb codom in
      dep, mkLambda(name,dom,body)
  | Vfun f, _ ->
      let k = nb_rel env in
      let vb = body_of_vfun k f in
      let name = Name (Id.of_string "c") in
      let n = mip.mind_nrealargs in
      let rargs = Array.init n (fun i -> mkRel (n-i)) in
      let params = if Int.equal n 0 then params else Array.map (lift n) params in
      let dom = mkApp(mkIndU ind,Array.append params rargs) in
      let body = nf_vtype (push_rel (name,None,dom) env) vb in
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
      Errors.anomaly
        (Pp.strbrk "Returned a functional value in a type not recognized as a product type.")
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

let pr_instance = Univ.Instance.pr Univ.Level.pr


let rec pr_constr c =
  Pp.(match kind_of_term c with
      | Rel i -> str "Rel(" ++ int i ++ str ")"
      | Var v -> str "Var(" ++ Id.print v ++ str ")"
      | Meta _ -> assert false
      | Evar _ -> assert false
      | Sort (Prop Pos) -> str "Sort(Set)"
      | Sort (Prop Null) -> str "Sort(Prop)"
      | Sort (Type u) -> str "Sort(Type@{" ++ Univ.pr_uni u ++ str "})"
      | Cast _ -> str "Cast"
      | LetIn (_,x,t,b) -> str "let : (" ++ pr_constr t ++ str ") := (" ++ pr_constr x ++ str ") in (" ++ pr_constr b ++ str ")"
      | App(f,xs) -> str "(" ++ pr_constr f ++ str " @ " ++ pr_sequence pr_constr (Array.to_list xs) ++ str ")"
      | Const (c,_) -> Names.pr_con c
      | Lambda (_,t,b) -> str "(\\" ++ pr_constr t ++ str " -> " ++ pr_constr b ++ str ")"
      | Ind ((mi,i),u) -> Names.pr_mind mi ++ str "#" ++ int i ++ str "@{" ++ pr_instance u ++ str "}"
      | Case _ -> str "Case"
      | Fix _ -> str "Fix"
      | CoFix _ -> str "CoFix"
      | Prod (_,d,c) -> str "Prod(" ++ pr_constr d ++ str ", " ++ pr_constr c ++ str ")"
      | Construct (((mi,i),id),u) -> str "Constructor(" ++ Names.pr_mind mi ++ str "#" ++ int i ++ str "#" ++ int id ++ str "@{" ++ pr_instance u ++ str "})"
      | Proj _ -> str "Proj"
      )


let cbv_vm env c t  =
  Printf.eprintf "cbv_vm >>>>>>>>>>>>>>>>>>>>>\n" ; flush stderr ;
  let transp = transp_values () in
  if not transp then set_transp_values true;
  Printf.eprintf "val_of_constr >>>>>>>>>>>>>>>>>>>>>\n" ; flush stderr ;
  let v = Vconv.val_of_constr env c in
  Printf.eprintf "val_of_constr <<<<<<<<<<<<<<<<<<<<<\n" ; flush stderr ;
  let c = nf_val env v t in
  Printf.eprintf "nf_val <<<<<<<<<<<<<<<<<<<<<\n" ; flush stderr ;
  Pp.(msg_debug (str "vm_result =" ++ fnl () ++ pr_constr c ++ fnl ()));
  if not transp then set_transp_values false;
  c
