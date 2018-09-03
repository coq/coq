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
open Esubst
open Constr
open Declarations
open Environ
open Nativevalues
open Nativeinstr

module RelDecl = Context.Rel.Declaration


exception NotClosed

type evars =
    { evars_val : existential -> constr option;
      evars_metas : metavariable -> types }

(*s Constructors *)

let mkLapp f args =
  if Array.is_empty args then f
  else
    match f with
    | Lapp(f', args') -> Lapp (f', Array.append args' args)
    | _ -> Lapp(f, args)

let mkLlam ids body =
  if Array.is_empty ids then body
  else 
    match body with
    | Llam(ids', body) -> Llam(Array.append ids ids', body)
    | _ -> Llam(ids, body)

let decompose_Llam lam =
  match lam with
  | Llam(ids,body) -> ids, body
  | _ -> [||], lam

let rec decompose_Llam_Llet lam =
  match lam with
  | Llam(ids,body) ->
      let vars, body = decompose_Llam_Llet body in
      Array.fold_right (fun x l -> (x, None) :: l) ids vars, body
  | Llet(id,def,body) ->
      let vars, body = decompose_Llam_Llet body in
      (id,Some def) :: vars, body
  | _ -> [], lam

let decompose_Llam_Llet lam =
  let vars, body = decompose_Llam_Llet lam in
  Array.of_list vars, body

(*s Operators on substitution *)
let subst_id = subs_id 0
let lift = subs_lift 
let liftn = subs_liftn
let cons v subst = subs_cons([|v|], subst)
let shift subst = subs_shft (1, subst)

(* Linked code location utilities *)
let get_mind_prefix env mind =
   let _,name = lookup_mind_key mind env in
   match !name with
   | NotLinked -> ""
   | Linked s -> s
   | LinkedInteractive s -> s

let get_const_prefix env c =
   let _,(nameref,_) = lookup_constant_key c env in
   match !nameref with
   | NotLinked -> ""
   | Linked s -> s
   | LinkedInteractive s -> s

(* A generic map function *)

let rec map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lproj _ | Lval _ | Lsort _ | Lind _
  | Lconstruct _ | Llazy | Lforce | Lmeta _ -> lam
  | Lprod(dom,codom) -> 
      let dom' = f n dom in
      let codom' = f n codom in
      if dom == dom' && codom == codom' then lam else Lprod(dom',codom')
  | Llam(ids,body) ->
      let body' = f (g (Array.length ids) n) body in
      if body == body' then lam else mkLlam ids body'
  | Llet(id,def,body) ->
      let def' = f n def in
      let body' = f (g 1 n) body in
      if body == body' && def == def' then lam else Llet(id,def',body')
  | Lapp(fct,args) ->
      let fct' = f n fct in
      let args' = Array.Smart.map (f n) args in
      if fct == fct' && args == args' then lam else mkLapp fct' args'
  | Lprim(prefix,kn,op,args) ->
      let args' = Array.Smart.map (f n) args in
      if args == args' then lam else Lprim(prefix,kn,op,args')
  | Lcase(annot,t,a,br) ->
      let t' = f n t in
      let a' = f n a in
      let on_b b = 
	let (cn,ids,body) = b in
	let body' = 
	  if Array.is_empty ids then f n body 
	  else f (g (Array.length ids) n) body in
	if body == body' then b else (cn,ids,body') in
      let br' = Array.Smart.map on_b br in
      if t == t' && a == a' && br == br' then lam else Lcase(annot,t',a',br')
  | Lif(t,bt,bf) ->
      let t' = f n t in
      let bt' = f n bt in
      let bf' = f n bf in
      if t == t' && bt == bt' && bf == bf' then lam else Lif(t',bt',bf')
  | Lfix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = Array.Smart.map (f n) ltypes in
      let lbodies' = Array.Smart.map (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lfix(init,(ids,ltypes',lbodies'))
  | Lcofix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = Array.Smart.map (f n) ltypes in
      let lbodies' = Array.Smart.map (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lcofix(init,(ids,ltypes',lbodies'))
  | Lmakeblock(prefix,cn,tag,args) ->
      let args' = Array.Smart.map (f n) args in
      if args == args' then lam else Lmakeblock(prefix,cn,tag,args')
  | Luint u ->
    let u' = map_uint g f n u in
    if u == u' then lam else Luint u'
  | Levar (evk, args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Levar (evk, args')

and map_uint g f n u =
  match u with
  | UintVal _ -> u
  | UintDigits(prefix,c,args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then u else UintDigits(prefix,c,args')
  | UintDecomp(prefix,c,a) ->
    let a' = f n a in
    if a == a' then u else UintDecomp(prefix,c,a')

(*s Lift and substitution *)
 
let rec lam_exlift el lam =
  match lam with
  | Lrel(id,i) -> 
      let i' = reloc_rel i el in
      if i == i' then lam else Lrel(id,i')
  | _ -> map_lam_with_binders el_liftn lam_exlift el lam

let lam_lift k lam =
  if Int.equal k 0 then lam
  else lam_exlift (el_shft k el_id) lam

let lam_subst_rel lam id n subst =
  match expand_rel n subst with
  | Inl(k,v) -> lam_lift k v
  | Inr(n',_) -> 
      if n == n' then lam
      else Lrel(id, n') 

let rec lam_exsubst subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst
  | _ -> map_lam_with_binders liftn lam_exsubst subst lam

let lam_subst_args subst args =
  if is_subs_id subst then args 
  else Array.Smart.map (lam_exsubst subst) args
  
(** Simplification of lambda expression *)
      
(* [simplify subst lam] simplify the expression [lam_subst subst lam] *)
(* that is :                                                          *)
(* - Reduce [let] is the definition can be substituted i.e:           *)
(*    - a variable (rel or identifier)                                *)
 (*    - a constant                                                    *)
(*    - a structured constant                                         *)
(*    - a function                                                    *)
(* - Transform beta redex into [let] expression                       *)
(* - Move arguments under [let]                                       *) 
(* Invariant : Terms in [subst] are already simplified and can be     *)
(*             substituted                                            *)
  
let can_subst lam = 
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Lproj _ | Lval _ | Lsort _ | Lind _ | Llam _
  | Lconstruct _ | Lmeta _ | Levar _ -> true
  | _ -> false

let can_merge_if bt bf =
  match bt, bf with
  | Llam(idst,_), Llam(idsf,_) -> true
  | _ -> false

let merge_if t bt bf =
  let (idst,bodyt) = decompose_Llam bt in
  let (idsf,bodyf) = decompose_Llam bf in
  let nt = Array.length idst in
  let nf = Array.length idsf in
  let common,idst,idsf = 
    if Int.equal nt nf then idst, [||], [||] 
    else
      if nt < nf then idst,[||], Array.sub idsf nt (nf - nt)
      else idsf, Array.sub idst nf (nt - nf), [||] in
  Llam(common,
       Lif(lam_lift (Array.length common) t, 
	   mkLlam idst bodyt,
	   mkLlam idsf bodyf))

let rec simplify subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst 

  | Llet(id,def,body) ->
      let def' = simplify subst def in
      if can_subst def' then simplify (cons def' subst) body
      else 
	let body' = simplify (lift subst) body in
	if def == def' && body == body' then lam
	else Llet(id,def',body')

  | Lapp(f,args) ->
      begin match simplify_app subst f subst args with
      | Lapp(f',args') when f == f' && args == args' -> lam
      | lam' -> lam'
      end

  | Lif(t,bt,bf) ->
      let t' = simplify subst t in
      let bt' = simplify subst bt in
      let bf' = simplify subst bf in
      if can_merge_if bt' bf' then merge_if t' bt' bf'
      else 
	if t == t' && bt == bt' && bf == bf' then lam
	else Lif(t',bt',bf')
  | _ -> map_lam_with_binders liftn simplify subst lam

and simplify_app substf f substa args =
  match f with
  | Lrel(id, i) ->
      begin match lam_subst_rel f id i substf with
      | Llam(ids, body) ->
	  reduce_lapp 
	    subst_id (Array.to_list ids) body  
	    substa (Array.to_list args)
      | f' -> mkLapp f' (simplify_args substa args)
      end
  | Llam(ids, body) ->
      reduce_lapp substf (Array.to_list ids) body substa (Array.to_list args)
  | Llet(id, def, body) ->
      let def' = simplify substf def in
      if can_subst def' then
	simplify_app (cons def' substf) body substa args
      else 
	Llet(id, def', simplify_app (lift substf) body (shift substa) args)
  | Lapp(f, args') ->
      let args = Array.append 
	  (lam_subst_args substf args') (lam_subst_args substa args) in
      simplify_app substf f subst_id args
  (* TODO | Lproj -> simplify if the argument is known or a known global *)
  | _ -> mkLapp (simplify substf f) (simplify_args substa args)
  
and simplify_args subst args = Array.Smart.map (simplify subst) args

and reduce_lapp substf lids body substa largs =
  match lids, largs with
  | id::lids, a::largs ->
      let a = simplify substa a in
      if can_subst a then
	reduce_lapp (cons a substf) lids body substa largs
      else
	let body = reduce_lapp (lift substf) lids body (shift substa) largs in
	Llet(id, a, body)
  | [], [] -> simplify substf body
  | _::_, _ -> 
      Llam(Array.of_list lids,  simplify (liftn (List.length lids) substf) body)
  | [], _::_ -> simplify_app substf body substa (Array.of_list largs)

(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match lc with
  | Lval _ -> true
  | Lmakeblock(_,_,_,args) when Array.is_empty args -> true
  | Luint (UintVal _) -> true
  | _ -> false

let get_value lc =
  match lc with
  | Lval v -> v
  | Lmakeblock(_,_,tag,args) when Array.is_empty args ->
      Nativevalues.mk_int tag
  | Luint (UintVal i) -> Nativevalues.mk_uint i
  | _ -> raise Not_found

let make_args start _end =
  Array.init (start - _end + 1) (fun i -> Lrel (Anonymous, start - i))
    
(* Translation of constructors *)	

let makeblock env cn u tag args =
  if Array.for_all is_value args && Array.length args > 0 then
    let args = Array.map get_value args in
    Lval (Nativevalues.mk_block tag args)
  else
    let prefix = get_mind_prefix env (fst (fst cn)) in
    Lmakeblock(prefix, (cn,u), tag, args)

(* Translation of constants *)

let rec get_alias env (kn, u as p) =
  let tps = (lookup_constant kn env).const_body_code in
    match tps with
    | None -> p
    | Some tps ->
       match Cemitcodes.force tps with
       | Cemitcodes.BCalias kn' -> get_alias env (kn', u)
       | _ -> p

(*i Global environment *)

let get_names decl = 
  let decl = Array.of_list decl in
  Array.map fst decl

let empty_args = [||]

module Cache =
  struct

    module ConstrHash =
    struct
      type t = constructor
      let equal = eq_constructor
      let hash = constructor_hash
    end

    module ConstrTable = Hashtbl.Make(ConstrHash)

    type constructor_info = tag * int * int (* nparam nrealargs *)

    let get_construct_info cache env c : constructor_info =
      try ConstrTable.find cache c
      with Not_found -> 
	let ((mind,j), i) = c in
        let oib = lookup_mind mind env in
	let oip = oib.mind_packets.(j) in
	let tag,arity = oip.mind_reloc_tbl.(i-1) in
	let nparams = oib.mind_nparams in
	let r = (tag, nparams, arity) in
        ConstrTable.add cache c r;
	r
  end

let is_lazy env prefix t =
  match kind t with
  | App (f,args) ->
     begin match kind f with
     | Construct (c,_) ->
	let entry = mkInd (fst c) in
	(try
	    let _ =
              Retroknowledge.get_native_before_match_info env.retroknowledge
							  entry prefix c Llazy;
	    in
	    false
	  with Not_found -> true)
     | _ -> true
     end
  | LetIn _ | Case _ | Proj _ -> true
  | _ -> false

let evar_value sigma ev = sigma.evars_val ev

let meta_type sigma mv = sigma.evars_metas mv

let empty_evars =
  { evars_val = (fun _ -> None);
    evars_metas = (fun _ -> assert false) }

let empty_ids = [||]

(** Extract the inductive type over which a fixpoint is decreasing *)
let rec get_fix_struct env i t = match kind (Reduction.whd_all env t) with
| Prod (na, dom, t) ->
  if Int.equal i 0 then
    let dom = Reduction.whd_all env dom in
    let (dom, _) = decompose_appvect dom in
    match kind dom with
    | Ind (ind, _) -> ind
    | _ -> assert false
  else
    let env = Environ.push_rel (RelDecl.LocalAssum (na, dom)) env in
    get_fix_struct env (i - 1) t
| _ -> assert false

let rec lambda_of_constr cache env sigma c =
  match kind c with
  | Meta mv ->
     let ty = meta_type sigma mv in
     Lmeta (mv, lambda_of_constr cache env sigma ty)

  | Evar (evk,args as ev) ->
     (match evar_value sigma ev with
     | None ->
        let args = Array.map (lambda_of_constr cache env sigma) args in
        Levar(evk, args)
     | Some t -> lambda_of_constr cache env sigma t)

  | Cast (c, _, _) -> lambda_of_constr cache env sigma c

  | Rel i -> Lrel (RelDecl.get_name (Environ.lookup_rel i env), i)

  | Var id -> Lvar id

  | Sort s -> Lsort s

  | Ind (ind,u as pind) ->
      let prefix = get_mind_prefix env (fst ind) in
      Lind (prefix, pind)

  | Prod(id, dom, codom) ->
      let ld = lambda_of_constr cache env sigma dom in
      let env = Environ.push_rel (RelDecl.LocalAssum (id, dom)) env in
      let lc = lambda_of_constr cache env sigma codom in
      Lprod(ld,  Llam([|id|], lc))

  | Lambda _ ->
      let params, body = Term.decompose_lam c in
      let fold (na, t) env = Environ.push_rel (RelDecl.LocalAssum (na, t)) env in
      let env = List.fold_right fold params env in
      let lb = lambda_of_constr cache env sigma body in
      let ids = get_names (List.rev params) in
      mkLlam ids lb

  | LetIn(id, def, t, body) ->
      let ld = lambda_of_constr cache env sigma def in
      let env = Environ.push_rel (RelDecl.LocalDef (id, def, t)) env in
      let lb = lambda_of_constr cache env sigma body in
      Llet(id, ld, lb)

  | App(f, args) -> lambda_of_app cache env sigma f args

  | Const _ -> lambda_of_app cache env sigma c empty_args

  | Construct _ ->  lambda_of_app cache env sigma c empty_args

  | Proj (p, c) ->
    let ind = Projection.inductive p in
    let prefix = get_mind_prefix env (fst ind) in
    mkLapp (Lproj (prefix, ind, Projection.arg p)) [|lambda_of_constr cache env sigma c|]

  | Case(ci,t,a,branches) ->  
      let (mind,i as ind) = ci.ci_ind in
      let mib = lookup_mind mind env in
      let oib = mib.mind_packets.(i) in
      let tbl = oib.mind_reloc_tbl in 
      (* Building info *)
      let prefix = get_mind_prefix env mind in
      let annot_sw = 
	    { asw_ind = ind;
          asw_ci = ci;
          asw_reloc = tbl; 
          asw_finite = mib.mind_finite <> CoFinite;
          asw_prefix = prefix}
      in
      (* translation of the argument *)
      let la = lambda_of_constr cache env sigma a in
      let entry = mkInd ind in
      let la =
	try
          Retroknowledge.get_native_before_match_info (env).retroknowledge
						      entry prefix (ind,1) la
	with Not_found -> la
      in
      (* translation of the type *)
      let lt = lambda_of_constr cache env sigma t in
      (* translation of branches *)
      let mk_branch i b =
	let cn = (ind,i+1) in
	let _, arity = tbl.(i) in
        let b = lambda_of_constr cache env sigma b in
	if Int.equal arity 0 then (cn, empty_ids, b)
	else 
	  match b with
	  | Llam(ids, body) when Int.equal (Array.length ids) arity -> (cn, ids, body)
	  | _ -> 
	      let ids = Array.make arity Anonymous in
	      let args = make_args arity 1 in
	      let ll = lam_lift arity b in
	      (cn, ids, mkLapp  ll args) in
      let bs = Array.mapi mk_branch branches in
      Lcase(annot_sw, lt, la, bs)
	
  | Fix((pos, i), (names,type_bodies,rec_bodies)) ->
      let ltypes = lambda_of_args cache env sigma 0 type_bodies in
      let map i t =
        let ind = get_fix_struct env i t in
        let prefix = get_mind_prefix env (fst ind) in
        (prefix, ind)
      in
      let inds = Array.map2 map pos type_bodies in
      let env = Environ.push_rec_types (names, type_bodies, rec_bodies) env in
      let lbodies = lambda_of_args cache env sigma 0 rec_bodies in
      Lfix((pos, inds, i), (names, ltypes, lbodies))
	
  | CoFix(init,(names,type_bodies,rec_bodies)) ->
      let rec_bodies = Array.map2 (Reduction.eta_expand env) rec_bodies type_bodies in
      let ltypes = lambda_of_args cache env sigma 0 type_bodies in
      let env = Environ.push_rec_types (names, type_bodies, rec_bodies) env in
      let lbodies = lambda_of_args cache env sigma 0 rec_bodies in
      Lcofix(init, (names, ltypes, lbodies))

and lambda_of_app cache env sigma f args =
  match kind f with
  | Const (kn,u as c) ->
      let kn,u = get_alias env c in
      let cb = lookup_constant kn env in
      (try
          let prefix = get_const_prefix env kn in
	  (* We delay the compilation of arguments to avoid an exponential behavior *)
	  let f = Retroknowledge.get_native_compiling_info
                    (env).retroknowledge (mkConst kn) prefix in
          let args = lambda_of_args cache env sigma 0 args in
	  f args
      with Not_found ->
      begin match cb.const_body with
      | Def csubst -> (* TODO optimize if f is a proj and argument is known *)
          if cb.const_inline_code then
            lambda_of_app cache env sigma (Mod_subst.force_constr csubst) args
          else
          let prefix = get_const_prefix env kn in
          let t =
            if is_lazy env prefix (Mod_subst.force_constr csubst) then
              mkLapp Lforce [|Lconst (prefix, (kn,u))|]
            else Lconst (prefix, (kn,u))
          in
        mkLapp t (lambda_of_args cache env sigma 0 args)
      | OpaqueDef _ | Undef _ ->
          let prefix = get_const_prefix env kn in
          mkLapp (Lconst (prefix, (kn,u))) (lambda_of_args cache env sigma 0 args)
      end)
  | Construct (c,u) ->
      let tag, nparams, arity = Cache.get_construct_info cache env c in
      let expected = nparams + arity in
      let nargs = Array.length args in
      let prefix = get_mind_prefix env (fst (fst c)) in
      if Int.equal nargs expected then 
      try
	try
	  Retroknowledge.get_native_constant_static_info
                         (env).retroknowledge
                         f args
          with NotClosed ->
	    assert (Int.equal nparams 0); (* should be fine for int31 *)
            let args = lambda_of_args cache env sigma nparams args in
	    Retroknowledge.get_native_constant_dynamic_info
                           (env).retroknowledge f prefix c args
        with Not_found ->
          let args = lambda_of_args cache env sigma nparams args in
          makeblock env c u tag args
      else
        let args = lambda_of_args cache env sigma 0 args in
	(try
	    Retroknowledge.get_native_constant_dynamic_info
              (env).retroknowledge f prefix c args
	  with Not_found ->
            mkLapp (Lconstruct (prefix, (c,u))) args)
  | _ -> 
      let f = lambda_of_constr cache env sigma f in
      let args = lambda_of_args cache env sigma 0 args in
      mkLapp f args
	
and lambda_of_args cache env sigma start args =
  let nargs = Array.length args in
  if start < nargs then
    Array.init (nargs - start) 
      (fun i -> lambda_of_constr cache env sigma args.(start + i))
  else empty_args

let optimize lam =
  let lam = simplify subst_id lam in
(*  if Flags.vm_draw_opt () then 
    (msgerrnl (str "Simplify = \n" ++ pp_lam lam);flush_all()); 
  let lam = remove_let subst_id lam in
  if Flags.vm_draw_opt () then 
    (msgerrnl (str "Remove let = \n" ++ pp_lam lam);flush_all()); *)
  lam

let lambda_of_constr env sigma c =
  let cache = Cache.ConstrTable.create 91 in
  let lam = lambda_of_constr cache env sigma c in
(*  if Flags.vm_draw_opt () then begin
    (msgerrnl (str "Constr = \n" ++ pr_constr c);flush_all()); 
    (msgerrnl (str "Lambda = \n" ++ pp_lam lam);flush_all()); 
  end; *)
  optimize lam

let mk_lazy c =
  mkLapp Llazy [|c|]

(** Retroknowledge, to be removed once we move to primitive machine integers *)
let compile_static_int31 fc args =
  if not fc then raise Not_found else
    Luint (UintVal
    (Uint31.of_int (Array.fold_left
       (fun temp_i -> fun t -> match kind t with
          | Construct ((_,d),_) -> 2*temp_i+d-1
          | _ -> raise NotClosed)
       0 args)))

let compile_dynamic_int31 fc prefix c args =
  if not fc then raise Not_found else
  Luint (UintDigits (prefix,c,args))

(* We are relying here on the order of digits constructors *)
let digits_from_uint digits_ind prefix i =
  let d0 = Lconstruct (prefix, ((digits_ind, 1), Univ.Instance.empty)) in
  let d1 = Lconstruct (prefix, ((digits_ind, 2), Univ.Instance.empty)) in
  let digits = Array.make 31 d0 in
  for k = 0 to 30 do
    if Int.equal ((Uint31.to_int i lsr k) land 1) 1 then
      digits.(30-k) <- d1
  done;
  digits

let before_match_int31 digits_ind fc prefix c t =
  if not fc then
    raise Not_found
  else
  match t with
  | Luint (UintVal i) ->
     let digits = digits_from_uint digits_ind prefix i in
     mkLapp (Lconstruct (prefix,(c, Univ.Instance.empty))) digits
  | Luint (UintDigits (prefix,c,args)) ->
     mkLapp (Lconstruct (prefix,(c, Univ.Instance.empty))) args
  | _ -> Luint (UintDecomp (prefix,c,t))

let compile_prim prim kn fc prefix args =
  if not fc then raise Not_found
  else
    Lprim(prefix, kn, prim, args)
