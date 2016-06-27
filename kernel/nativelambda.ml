(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Util
open Names
open Esubst
open Term
open Declarations
open Pre_env
open Nativevalues
open Nativeinstr

(** This file defines the lambda code generation phase of the native compiler *)

exception NotClosed

type evars =
    { evars_val : existential -> constr option;
      evars_typ : existential -> types;
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

let map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lproj _ | Luint _ | Lval _ | Lsort _ | Lind _
  | Lconstruct _ | Llazy | Lforce | Lmeta _ | Levar _ -> lam
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
      let args' = Array.smartmap (f n) args in
      if fct == fct' && args == args' then lam else mkLapp fct' args'
  | Lprim(prefix,kn,op,args) ->
      let args' = Array.smartmap (f n) args in
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
      let br' = Array.smartmap on_b br in
      if t == t' && a == a' && br == br' then lam else Lcase(annot,t',a',br')
  | Lif(t,bt,bf) ->
      let t' = f n t in
      let bt' = f n bt in
      let bf' = f n bf in
      if t == t' && bt == bt' && bf == bf' then lam else Lif(t',bt',bf')
  | Lfix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = Array.smartmap (f n) ltypes in
      let lbodies' = Array.smartmap (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lfix(init,(ids,ltypes',lbodies'))
  | Lcofix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = Array.smartmap (f n) ltypes in
      let lbodies' = Array.smartmap (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lcofix(init,(ids,ltypes',lbodies'))
  | Lmakeblock(prefix,cn,tag,args) ->
      let args' = Array.smartmap (f n) args in
      if args == args' then lam else Lmakeblock(prefix,cn,tag,args')

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

let lam_subst subst lam =
  if is_subs_id subst then lam
  else lam_exsubst subst lam

let lam_subst_args subst args =
  if is_subs_id subst then args 
  else Array.smartmap (lam_exsubst subst) args
  
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
  
and simplify_args subst args = Array.smartmap (simplify subst) args

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


(* [occurrence kind k lam]:
   If [kind] is [true] return [true] if the variable [k] does not appear in 
   [lam], return [false] if the variable appear one time and not
   under a lambda, a fixpoint, a cofixpoint; else raise Not_found.
   If [kind] is [false] return [false] if the variable does not appear in [lam]
   else raise [Not_found]
*)

let rec occurrence k kind lam =
  match lam with
  | Lrel (_,n) -> 
      if Int.equal n k then 
	if kind then false else raise Not_found
      else kind
  | Lvar _  | Lconst _  | Lproj _ | Luint _ | Lval _ | Lsort _ | Lind _
  | Lconstruct _ | Llazy | Lforce | Lmeta _ | Levar _ -> kind
  | Lprod(dom, codom) ->
      occurrence k (occurrence k kind dom) codom
  | Llam(ids,body) ->
      let _ = occurrence (k+Array.length ids) false body in kind
  | Llet(_,def,body) ->
      occurrence (k+1) (occurrence k kind def) body
  | Lapp(f, args) ->
      occurrence_args k (occurrence k kind f) args
  | Lprim(_,_,_,args) | Lmakeblock(_,_,_,args) ->
      occurrence_args k kind args
  | Lcase(_,t,a,br) ->
      let kind = occurrence k (occurrence k kind t) a in
      let r = ref kind in
      Array.iter (fun (_,ids,c) -> 
	r := occurrence (k+Array.length ids) kind c && !r) br;
      !r 
  | Lif (t, bt, bf) ->
      let kind = occurrence k kind t in
      kind && occurrence k kind bt && occurrence k kind bf
  | Lfix(_,(ids,ltypes,lbodies)) 
  | Lcofix(_,(ids,ltypes,lbodies)) ->
      let kind = occurrence_args k kind ltypes in
      let _ = occurrence_args (k+Array.length ids) false lbodies in
      kind 

and occurrence_args k kind args =
  Array.fold_left (occurrence k) kind args
    
let occur_once lam = 
  try let _ = occurrence 1 true lam in true
  with Not_found -> false
      
(* [remove_let lam] remove let expression in [lam] if the variable is *)
(* used at most once time in the body, and does not appear under      *)
(* a lambda or a fix or a cofix                                       *)
      
let rec remove_let subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst 
  | Llet(id,def,body) ->
      let def' = remove_let subst def in
      if occur_once body then remove_let (cons def' subst) body
      else 
	let body' = remove_let (lift subst) body in
	if def == def' && body == body' then lam else Llet(id,def',body')
  | _ -> map_lam_with_binders liftn remove_let subst lam


(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match lc with
  | Lval _ -> true
  | Lmakeblock(_,_,_,args) when Array.is_empty args -> true
  | _ -> false
	
let get_value lc =
  match lc with
  | Lval v -> v
  | Lmakeblock(_,_,tag,args) when Array.is_empty args -> 
      Nativevalues.mk_int tag
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

let global_env = ref empty_env 

let set_global_env env = global_env := env

let get_names decl = 
  let decl = Array.of_list decl in
  Array.map fst decl

(* Rel Environment *)
module Vect = 
  struct
    type 'a t = {
	mutable elems : 'a array;
	mutable size : int;
      }

    let make n a = {
      elems = Array.make n a;
      size = 0;
    }

    let length v = v.size

    let extend v =
      if Int.equal v.size (Array.length v.elems) then 
	let new_size = min (2*v.size) Sys.max_array_length in
	if new_size <= v.size then invalid_arg "Vect.extend";
	let new_elems = Array.make new_size v.elems.(0) in
	Array.blit v.elems 0 new_elems 0 (v.size);
	v.elems <- new_elems

    let push v a = 
      extend v;
      v.elems.(v.size) <- a;
      v.size <- v.size + 1

    let push_pos v a =
      let pos = v.size in
      push v a;
      pos

    let popn v n =
      v.size <- max 0 (v.size - n)

    let pop v = popn v 1
	
    let get v n =
      if v.size <= n then invalid_arg "Vect.get:index out of bounds";
      v.elems.(n)

    let get_last v n =
      if v.size <= n then invalid_arg "Vect.get:index out of bounds";
      v.elems.(v.size - n - 1)


    let last v =
      if Int.equal v.size 0 then invalid_arg "Vect.last:index out of bounds";
      v.elems.(v.size - 1)

    let clear v = v.size <- 0

    let to_array v = Array.sub v.elems 0 v.size
      
  end

let empty_args = [||]

module Renv = 
  struct

    module ConstrHash =
    struct
      type t = constructor
      let equal = eq_constructor
      let hash = constructor_hash
    end

    module ConstrTable = Hashtbl.Make(ConstrHash)

    type constructor_info = tag * int * int (* nparam nrealargs *)

    type t = {
	name_rel : name Vect.t;
	construct_tbl : constructor_info ConstrTable.t;

       }


    let make () = {
      name_rel = Vect.make 16 Anonymous;
      construct_tbl = ConstrTable.create 111
    }

    let push_rel env id = Vect.push env.name_rel id

    let push_rels env ids = 
      Array.iter (push_rel env) ids

    let pop env = Vect.pop env.name_rel
	    
    let popn env n =
      for _i = 1 to n do pop env done

    let get env n =
      Lrel (Vect.get_last env.name_rel (n-1), n)

    let get_construct_info env c =
      try ConstrTable.find env.construct_tbl c
      with Not_found -> 
	let ((mind,j), i) = c in
	let oib = lookup_mind mind !global_env in
	let oip = oib.mind_packets.(j) in
	let tag,arity = oip.mind_reloc_tbl.(i-1) in
	let nparams = oib.mind_nparams in
	let r = (tag, nparams, arity) in
	ConstrTable.add env.construct_tbl c r;
	r
  end

(* What about pattern matching ?*)
let is_lazy prefix t =
  match kind_of_term t with
  | App (f,args) ->
     begin match kind_of_term f with
     | Construct (c,_) ->
	let entry = mkInd (fst c) in
	(try
	    let _ =
	      Retroknowledge.get_native_before_match_info (!global_env).retroknowledge
							  entry prefix c Llazy;
	    in
	    false
	  with Not_found -> true)
     | _ -> true
     end
  | LetIn _ -> true
  | _ -> false

let evar_value sigma ev = sigma.evars_val ev

let evar_type sigma ev = sigma.evars_typ ev

let meta_type sigma mv = sigma.evars_metas mv

let empty_evars =
  { evars_val = (fun _ -> None);
    evars_typ = (fun _ -> assert false);
    evars_metas = (fun _ -> assert false) }

let empty_ids = [||]

let rec lambda_of_constr env sigma c =
  match kind_of_term c with
  | Meta mv ->
     let ty = meta_type sigma mv in
     Lmeta (mv, lambda_of_constr env sigma ty)

  | Evar ev ->
     (match evar_value sigma ev with
     | None ->
	let ty = evar_type sigma ev in
	Levar(ev, lambda_of_constr env sigma ty)
     | Some t -> lambda_of_constr env sigma t)

  | Cast (c, _, _) -> lambda_of_constr env sigma c

  | Rel i -> Renv.get env i

  | Var id -> Lvar id

  | Sort s -> Lsort s

  | Ind (ind,u as pind) ->
      let prefix = get_mind_prefix !global_env (fst ind) in
      Lind (prefix, pind)

  | Prod(id, dom, codom) ->
      let ld = lambda_of_constr env sigma dom in
      Renv.push_rel env id;
      let lc = lambda_of_constr env sigma codom in
      Renv.pop env;
      Lprod(ld,  Llam([|id|], lc))

  | Lambda _ ->
      let params, body = decompose_lam c in
      let ids = get_names (List.rev params) in
      Renv.push_rels env ids;
      let lb = lambda_of_constr env sigma body in
      Renv.popn env (Array.length ids);
      mkLlam ids lb

  | LetIn(id, def, _, body) ->
      let ld = lambda_of_constr env sigma def in
      Renv.push_rel env id;
      let lb = lambda_of_constr env sigma body in
      Renv.pop env;
      Llet(id, ld, lb)

  | App(f, args) -> lambda_of_app env sigma f args

  | Const _ -> lambda_of_app env sigma c empty_args

  | Construct _ ->  lambda_of_app env sigma c empty_args

  | Proj (p, c) ->
    let kn = Projection.constant p in
      mkLapp (Lproj (get_const_prefix !global_env kn, kn)) [|lambda_of_constr env sigma c|]

  | Case(ci,t,a,branches) ->  
      let (mind,i as ind) = ci.ci_ind in
      let mib = lookup_mind mind !global_env in
      let oib = mib.mind_packets.(i) in
      let tbl = oib.mind_reloc_tbl in 
      (* Building info *)
      let prefix = get_mind_prefix !global_env mind in
      let annot_sw = 
	    { asw_ind = ind;
          asw_ci = ci;
          asw_reloc = tbl; 
          asw_finite = mib.mind_finite <> Decl_kinds.CoFinite;
          asw_prefix = prefix}
      in
      (* translation of the argument *)
      let la = lambda_of_constr env sigma a in
      let entry = mkInd ind in
      let la =
	try
	  Retroknowledge.get_native_before_match_info (!global_env).retroknowledge
						      entry prefix (ind,1) la
	with Not_found -> la
      in
      (* translation of the type *)
      let lt = lambda_of_constr env sigma t in
      (* translation of branches *)
      let mk_branch i b =
	let cn = (ind,i+1) in
	let _, arity = tbl.(i) in
	let b = lambda_of_constr env sigma b in
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
	
  | Fix(rec_init,(names,type_bodies,rec_bodies)) ->
      let ltypes = lambda_of_args env sigma 0 type_bodies in
      Renv.push_rels env names;
      let lbodies = lambda_of_args env sigma 0 rec_bodies in
      Renv.popn env (Array.length names);
      Lfix(rec_init, (names, ltypes, lbodies))
	
  | CoFix(init,(names,type_bodies,rec_bodies)) ->
      let ltypes = lambda_of_args env sigma 0 type_bodies in 
      Renv.push_rels env names;
      let lbodies = lambda_of_args env sigma 0 rec_bodies in
      Renv.popn env (Array.length names);
      Lcofix(init, (names, ltypes, lbodies))

and lambda_of_app env sigma f args =
  match kind_of_term f with
  | Const (kn,u as c) ->
      let kn,u = get_alias !global_env c in
      let cb = lookup_constant kn !global_env in
      (try
          let prefix = get_const_prefix !global_env kn in
	  (* We delay the compilation of arguments to avoid an exponential behavior *)
	  let f = Retroknowledge.get_native_compiling_info
		    (!global_env).retroknowledge (mkConst kn) prefix in
	  let args = lambda_of_args env sigma 0 args in
	  f args
      with Not_found ->
      begin match cb.const_body with
      | Def csubst -> (* TODO optimize if f is a proj and argument is known *)
          if cb.const_inline_code then
            lambda_of_app env sigma (Mod_subst.force_constr csubst) args
          else
          let prefix = get_const_prefix !global_env kn in
          let t =
            if is_lazy prefix (Mod_subst.force_constr csubst) then
              mkLapp Lforce [|Lconst (prefix, (kn,u))|]
            else Lconst (prefix, (kn,u))
          in
        mkLapp t (lambda_of_args env sigma 0 args)
      | OpaqueDef _ | Undef _ ->
          let prefix = get_const_prefix !global_env kn in
          mkLapp (Lconst (prefix, (kn,u))) (lambda_of_args env sigma 0 args)
      end)
  | Construct (c,u) ->
      let tag, nparams, arity = Renv.get_construct_info env c in
      let expected = nparams + arity in
      let nargs = Array.length args in
      let prefix = get_mind_prefix !global_env (fst (fst c)) in
      if Int.equal nargs expected then 
      try
	try
	  Retroknowledge.get_native_constant_static_info
                         (!global_env).retroknowledge
                         f args
          with NotClosed ->
	    assert (Int.equal nparams 0); (* should be fine for int31 *)
	    let args = lambda_of_args env sigma nparams args in
	    Retroknowledge.get_native_constant_dynamic_info
                           (!global_env).retroknowledge f prefix c args
        with Not_found ->
	  let args = lambda_of_args env sigma nparams args in
	  makeblock !global_env c u tag args
      else
	let args = lambda_of_args env sigma 0 args in
	(try
	    Retroknowledge.get_native_constant_dynamic_info
              (!global_env).retroknowledge f prefix c args
	  with Not_found ->
            mkLapp (Lconstruct (prefix, (c,u))) args)
  | _ -> 
      let f = lambda_of_constr env sigma f in
      let args = lambda_of_args env sigma 0 args in
      mkLapp f args
	
and lambda_of_args env sigma start args =
  let nargs = Array.length args in
  if start < nargs then
    Array.init (nargs - start) 
      (fun i -> lambda_of_constr env sigma args.(start + i))
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
  set_global_env env;
  let env = Renv.make () in
  let open Context.Rel.Declaration in
  let ids = List.rev_map get_name !global_env.env_rel_context in
  Renv.push_rels env (Array.of_list ids);
  let lam = lambda_of_constr env sigma c in
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
       (fun temp_i -> fun t -> match kind_of_term t with
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
