(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Nameops
open Univ
open Term
open Termops
open Sign
open Pre_env
open Environ
open Evd
open Reductionops
open Pretype_errors

(* Expanding existential variables (pretyping.ml) *)
(* 1- whd_ise fails if an existential is undefined *)

exception Uninstantiated_evar of existential_key

let rec whd_ise sigma c =
  match kind_of_term c with
    | Evar (ev,args) when Evd.mem sigma ev ->
	if Evd.is_defined sigma ev then
          whd_ise sigma (existential_value sigma (ev,args))
	else raise (Uninstantiated_evar ev)
  | _ -> c


(* Expand evars, possibly in the head of an application *)
let whd_castappevar_stack sigma c = 
  let rec whrec (c, l as s) =
    match kind_of_term c with
      | Evar (ev,args) when Evd.mem sigma ev & Evd.is_defined sigma ev -> 
	  whrec (existential_value sigma (ev,args), l)
      | Cast (c,_,_) -> whrec (c, l)
      | App (f,args) -> whrec (f, Array.fold_right (fun a l -> a::l) args l)
      | _ -> s
  in 
  whrec (c, [])

let whd_castappevar sigma c = applist (whd_castappevar_stack sigma c)

let nf_evar = Pretype_errors.nf_evar
let j_nf_evar = Pretype_errors.j_nf_evar
let jl_nf_evar = Pretype_errors.jl_nf_evar
let jv_nf_evar = Pretype_errors.jv_nf_evar
let tj_nf_evar = Pretype_errors.tj_nf_evar

let nf_evar_info evc info =
  { info with 
    evar_concl = Reductionops.nf_evar evc info.evar_concl;
    evar_hyps = map_named_val (Reductionops.nf_evar evc) info.evar_hyps}

let nf_evars evm = Evd.fold (fun ev evi evm' -> Evd.add evm' ev (nf_evar_info evm evi))
		     evm Evd.empty

let nf_evar_defs isevars = Evd.evars_reset_evd (nf_evars (Evd.evars_of isevars)) isevars

let nf_isevar isevars = nf_evar (Evd.evars_of isevars)
let j_nf_isevar isevars = j_nf_evar (Evd.evars_of isevars)
let jl_nf_isevar isevars = jl_nf_evar (Evd.evars_of isevars)
let jv_nf_isevar isevars = jv_nf_evar (Evd.evars_of isevars)
let tj_nf_isevar isevars = tj_nf_evar (Evd.evars_of isevars)

(**********************)
(* Creating new metas *)
(**********************)

(* Generator of metavariables *)
let new_meta =
  let meta_ctr = ref 0 in
  fun () -> incr meta_ctr; !meta_ctr

let mk_new_meta () = mkMeta(new_meta())

let collect_evars emap c =
  let rec collrec acc c =
    match kind_of_term c with
      | Evar (k,_) ->
	  if Evd.mem emap k & not (Evd.is_defined emap k) then k::acc
	  else (* No recursion on the evar instantiation *) acc
      | _         ->
	  fold_constr collrec acc c in
  list_uniquize (collrec [] c)

let push_dependent_evars sigma emap =
  Evd.fold (fun ev {evar_concl = ccl} (sigma',emap') ->
    List.fold_left 
      (fun (sigma',emap') ev -> 
	(Evd.add sigma' ev (Evd.find emap' ev),Evd.remove emap' ev))
      (sigma',emap') (collect_evars emap' ccl))
    emap (sigma,emap)

(* replaces a mapping of existentials into a mapping of metas.
   Problem if an evar appears in the type of another one (pops anomaly) *)
let evars_to_metas sigma (emap, c) =
  let emap = nf_evars emap in
  let sigma',emap' = push_dependent_evars sigma emap in
  let change_exist evar =
    let ty = nf_betaiota (nf_evar emap (existential_type emap evar)) in
    let n = new_meta() in
    mkCast (mkMeta n, DEFAULTcast, ty) in
  let rec replace c =
    match kind_of_term c with
        Evar (k,_ as ev) when Evd.mem emap' k -> change_exist ev
      | _ -> map_constr replace c in
  (sigma', replace c)

(* The list of non-instantiated existential declarations *)

let non_instantiated sigma = 
  let listev = to_list sigma in
  List.fold_left 
    (fun l (ev,evd) -> 
       if evd.evar_body = Evar_empty then 
	 ((ev,nf_evar_info sigma evd)::l) else l)
    [] listev

(**********************)
(* Creating new evars *)
(**********************)

(* Generator of existential names *)
let new_untyped_evar =
  let evar_ctr = ref 0 in
  fun () -> incr evar_ctr; existential_of_int !evar_ctr

(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

let new_evar_instance sign evd typ ?(src=(dummy_loc,InternalHole)) instance =
  assert
    (let ctxt = named_context_of_val sign in
     List.length instance = named_context_length ctxt &
     list_distinct (ids_of_named_context ctxt));
  let newev = new_untyped_evar() in
  let evd = evar_declare sign newev typ ~src:src evd in
  (evd,mkEvar (newev,Array.of_list instance))

(* Knowing that [Gamma |- ev : T] and that [ev] is applied to [args],
 * [make_projectable_subst ev args] builds the substitution [Gamma:=args].
 * If a variable and an alias of it are bound to the same instance, we skip
 * the alias (we just use eq_constr -- instead of conv --, since anyway,
 * only instances that are variables -- or evars -- are later considered;
 * morever, we can bet that similar instances came at some time from
 * the very same substitution. The removal of aliased duplicates is
 * useful to ensure the uniqueness of a projection.
*)

let make_projectable_subst sigma evi args =
  let sign = evar_context evi in
  let rec alias_of_var id = 
    match pi2 (Sign.lookup_named id sign) with
    | Some t when isVar t -> alias_of_var (destVar t)
    | _ -> id in
  snd (Sign.fold_named_context
    (fun (id,b,c) (args,l) ->
       match b, args with
	 | Some c, a::rest when
	     isVar c & eq_constr a (snd (List.assoc (destVar c) l)) -> (rest,l)
	 | _, a::rest -> (rest, (id, (alias_of_var id,whd_evar sigma a))::l)
	 | _ -> anomaly "Instance does not match its signature")
    sign ~init:(List.rev (Array.to_list args),[]))

let make_pure_subst evi args =
  snd (Sign.fold_named_context
    (fun (id,b,c) (args,l) ->
       match args with
	 | a::rest -> (rest, (id,a)::l)
	 | _ -> anomaly "Instance does not match its signature")
    (evar_context evi) ~init:(List.rev (Array.to_list args),[]))

(* [push_rel_context_to_named_context] builds the defining context and the
 * initial instance of an evar. If the evar is to be used in context
 * 
 * Gamma =  a1     ...    an xp      ...       x1
 *          \- named part -/ \- de Bruijn part -/
 * 
 * then the x1...xp are turned into variables so that the evar is declared in
 * context 
 *
 *          a1     ...    an xp      ...       x1
 *          \----------- named part ------------/
 *
 * but used applied to the initial instance "a1 ... an Rel(p) ... Rel(1)"
 * so that ev[a1:=a1 ... an:=an xp:=Rel(p) ... x1:=Rel(1)] is correctly typed
 * in context Gamma.
 * 
 * Remark 1: The instance is reverted in practice (i.e. Rel(1) comes first)
 * Remark 2: If some of the ai or xj are definitions, we keep them in the
 *   instance. This is necessary so that no unfolding of local definitions
 *   happens when inferring implicit arguments (consider e.g. the problem
 *   "x:nat; x':=x; f:forall x, x=x -> Prop |- f _ (refl_equal x')"
 *   we want the hole to be instantiated by x', not by x (which would have the
 *   case in [real_clean] if x' had disappear of the instance).
 *   Note that at any time, if, in some context env, the instance of
 *   declaration x:A is t and the instance of definition x':=phi(x) is u, then 
 *   we have the property that u and phi(t) are convertible in env.
 *)

let push_rel_context_to_named_context env typ =
  (* compute the instances relative to the named context and rel_context *)
  let ids = List.map pi1 (named_context env) in
  let inst_vars = List.map mkVar ids in
  let inst_rels = List.rev (rel_list 0 (nb_rel env)) in
  (* move the rel context to a named context and extend the named instance *)
  (* with vars of the rel context *)
  (* We do keep the instances corresponding to local definition (see above) *)
  let (subst, _, env) =
    Sign.fold_rel_context
      (fun (na,c,t) (subst, avoid, env) ->
	let id = next_name_away na avoid in
	let d = (id,option_map (substl subst) c,substl subst t) in
	(mkVar id :: subst, id::avoid, push_named d env))
      (rel_context env) ~init:([], ids, env) in
  (named_context_val env, substl subst typ, inst_rels@inst_vars)
      
(* [new_evar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)

let new_evar evd env ?(src=(dummy_loc,InternalHole)) typ =
  let sign,typ',instance = push_rel_context_to_named_context env typ in
    new_evar_instance sign evd typ' ~src:src instance

  (* The same using side-effect *)
let e_new_evar evd env ?(src=(dummy_loc,InternalHole)) ty =
  let (evd',ev) = new_evar !evd env ~src:src ty in
    evd := evd';
    ev

(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

(* Pb: defined Rels and Vars should not be considered as a pattern... *)
let is_pattern inst =
  let rec is_hopat l = function
      [] -> true
    | t :: tl ->
        (isRel t or isVar t) && not (List.mem t l) && is_hopat (t::l) tl in
  is_hopat [] (Array.to_list inst)

let evar_well_typed_body evd ev evi body =
  try
    let env = evar_env evi in
    let ty = evi.evar_concl in
    Typing.check env (evars_of evd) body ty;
    true
  with e ->
    pperrnl
      (str "Ill-typed evar instantiation: " ++ fnl() ++
       pr_evar_defs evd ++ fnl() ++
       str "----> " ++ int ev ++ str " := " ++
       print_constr body);
    false

let strict_inverse = false

let inverse_instance env isevars ev evi inst rhs =
  let subst = make_projectable_subst (evars_of isevars) evi inst in
  let subst = List.map (fun (x,(_,y)) -> (y,mkVar x)) subst in
  let evd = ref isevars in
  let error () = 
    error_not_clean env (evars_of !evd) ev rhs (evar_source ev !evd) in
  let rec subs rigid k t =
    match kind_of_term t with
      | Rel i ->
 	  if i<=k then t
 	  else
            (try List.assoc (mkRel (i-k)) subst
             with Not_found ->
               if rigid then error()
               else if strict_inverse then
                 failwith "cannot solve pb yet"
               else t)
      | Var id ->
          (try List.assoc t subst
           with Not_found ->
             if rigid then error()
             else if
               not strict_inverse &&
               List.exists (fun (id',_,_) -> id=id') (evar_context evi)
             then
               failwith "cannot solve pb yet"
             else t)
      | Evar (ev,args) ->
          if Evd.is_defined_evar !evd (ev,args) then
            subs rigid k (existential_value (evars_of !evd) (ev,args))
          else
	    let args' = Array.map (subs false k) args in
	    mkEvar (ev,args')
      | _ -> map_constr_with_binders succ (subs rigid) k t in
  let body = subs true 0 (nf_evar (evars_of isevars) rhs) in
  (!evd,body)


let is_defined_equation env evd (ev,inst) rhs =
  is_pattern inst &&
  not (occur_evar ev rhs) &&
  try
    let evi = Evd.find (evars_of evd) ev in
    let (evd',body) = inverse_instance env evd ev evi inst rhs in
    evar_well_typed_body evd' ev evi body
  with Failure _ -> false


(* Redefines an evar with a smaller context (i.e. it may depend on less
 * variables) such that c becomes closed.
 * Example: in "fun (x:?1) (y:list ?2) => x = y :> ?3 /\ x = nil bool"
 * ?3 <-- ?1          no pb: env of ?3 is larger than ?1's
 * ?1 <-- list ?2     pb: ?2 may depend on x, but not ?1.
 * What we do is that ?2 is defined by a new evar ?4 whose context will be
 * a prefix of ?2's env, included in ?1's env.
 *
 * Concretely, the assumptions are "env |- ev : T" and "Gamma |-
 * ev[hyps:=args]" for some Gamma whose de Bruijn context has length k.
 * We create "env' |- ev' : T" for some env' <= env and define ev:=ev'
*)

let do_restrict_hyps env k evd ev args =
  let args = Array.to_list args in
  let evi = Evd.find (evars_of !evd) ev in
  let hyps = evar_context evi in
  let (hyps',ncargs) = list_filter2 (fun _ a -> closedn k a) (hyps,args) in
    (* No care is taken in case the evar type uses vars filtered out!
       Assuming that the restriction comes from a well-typed Flex/Flex
       unification problem (see real_clean), the type of the evar cannot
       depend on variables that are not in the scope of the other evar,
       since this other evar has the same type (up to unification).
     Since moreover, the evar contexts uses names only, the
       restriction raise no de Bruijn reallocation problem *)
  let env' =
    Sign.fold_named_context push_named hyps' ~init:(reset_context env) in
  let nc = e_new_evar evd env' ~src:(evar_source ev !evd) evi.evar_concl in
    evd := Evd.evar_define ev nc !evd;
    let (evn,_) = destEvar nc in
      mkEvar(evn,Array.of_list ncargs)

exception Dependency_error of identifier
	
let rec check_and_clear_in_constr evd c ids =
  (* returns a new constr where all the evars have been 'cleaned'
     (ie the hypotheses ids have been removed from the contexts of
     evars *)
  let check id' = 
    if List.mem id' ids then
      raise (Dependency_error id')
  in 
    match kind_of_term c with
      | ( Rel _ | Meta _ | Sort _ ) -> c
      | ( Const _ | Ind _ | Construct _ ) -> 
	  let vars = Environ.vars_of_global (Global.env()) c in
	    List.iter check vars; c
      | Var id' ->  
	  check id'; mkVar id'
      | Evar (e,l) -> 
	  if Evd.is_defined_evar !evd (e,l) then
	    (* If e is already defined we replace it by its definition *)
	    let nc = nf_evar (evars_of !evd) c in 
	      (check_and_clear_in_constr evd nc ids)
	  else
	    (* We check for dependencies to elements of ids in the
	       evar_info corresponding to e and in the instance of
	       arguments. Concurrently, we build a new evar
	       corresponding to e where hypotheses of ids have been
	       removed *)
	    let evi = Evd.find (evars_of !evd) e in
	    let nconcl = check_and_clear_in_constr evd (evar_concl evi) ids in
	    let (nhyps,nargs) = 
	      List.fold_right2 
		(fun (id,ob,c) i (hy,ar) ->
		  if List.mem id ids then
		    (hy,ar)
		  else
		    let d' = (id,
			     (match ob with 
				 None -> None
			       | Some b -> Some (check_and_clear_in_constr evd b ids)),
			     check_and_clear_in_constr evd c ids) in
		    let i' = check_and_clear_in_constr evd i ids in
		      (d'::hy, i'::ar)
		) 	      
		(evar_context evi) (Array.to_list l) ([],[]) in
	    let env = Sign.fold_named_context push_named nhyps ~init:(empty_env) in
	    let ev'= e_new_evar evd env ~src:(evar_source e !evd) nconcl in
	      evd := Evd.evar_define e ev' !evd;
	      let (e',_) = destEvar ev' in
		mkEvar(e', Array.of_list nargs)
      | _ -> map_constr (fun c -> check_and_clear_in_constr evd c ids) c

and clear_hyps_in_evi evd evi ids =
  (* clear_evar_hyps erases hypotheses ids in evi, checking if some
     hypothesis does not depend on a element of ids, and erases ids in
     the contexts of the evars occuring in evi *)
  let nconcl = try check_and_clear_in_constr evd (evar_concl evi) ids 
    with Dependency_error id' -> error (string_of_id id' ^ " is used in conclusion") in
  let (nhyps,_) = 
    let check_context (id,ob,c) = 
      try
	(id,
	(match ob with 
	    None -> None
	  | Some b -> Some (check_and_clear_in_constr evd b ids)),
	check_and_clear_in_constr evd c ids)
      with Dependency_error id' -> error (string_of_id id' ^ " is used in hypothesis "
					   ^ string_of_id id) 
    in
    let check_value vk =
      match !vk with
	| VKnone -> vk
	| VKvalue (v,d) ->
	    if (List.for_all (fun e -> not (Idset.mem e d)) ids) then
	      (* v does depend on any of ids, it's ok *)
	      vk
	    else
	      (* v depends on one of the cleared hyps: we forget the computed value *)
	      ref VKnone
    in
      remove_hyps ids check_context check_value (evar_hyps evi)
  in    
    { evi with
	evar_concl = nconcl;
	evar_hyps  = nhyps}

let need_restriction k args = not (array_for_all (closedn k) args)

(* [find_projectable_vars env sigma y subst] finds all vars of [subst]
 * that project on [y] up to variables aliasing.  In case of solutions that
 * differ only up to aliasing, the binding that requires the less
 * steps of alias reduction is kept. At the end, only one solution up
 * to aliasing is kept.
 *
 * [find_projectable_vars] also unifies against evars that themselves mention
 * [y] and recursively.
 *
 * In short, the following situations give the following solutions:
 *
 * problem                        evar ctxt   soluce remark
 * z1; z2:=z1 |- ?ev[z1;z2] = z1  y1:A; y2:=y1  y1  \ thanks to defs kept in
 * z1; z2:=z1 |- ?ev[z1;z2] = z2  y1:A; y2:=y1  y2  / subst and preferring =
 * z1; z2:=z1 |- ?ev[z1]    = z2  y1:A          y1  thanks to is_conv
 * z1; z2:=z1 |- ?ev[z2]    = z1  y1:A          y1  thanks to is_conv
 * z3         |- ?ev[z3;z3] = z3  y1:A; y2:=y1  y2  see make_projectable_subst
 *
 * Remark: [find_projectable_vars] assumes that identical instances of
 * variables in the same set of aliased variables are already removed (see
 * [make_projectable_subst])
 *)

type evar_projection = 
| ProjectVar 
| ProjectEvar of existential * evar_info * (identifier * evar_projection) list

let rec find_projectable_vars env sigma y subst =
  let is_projectable (id,(idc,y')) =
    if is_conv env sigma y y' then (idc,(y'=y,(id,ProjectVar)))
    else if isEvar y' then
      let (ev,argsv as t) = destEvar y' in
      let evi = Evd.find sigma ev in
      let subst = make_projectable_subst sigma evi argsv in
      let l = find_projectable_vars env sigma y subst in
      if l <> [] then (idc,(true,(id,ProjectEvar (t,evi,l))))
      else failwith ""
    else failwith "" in
  let l = map_succeed is_projectable subst in
  let l = list_partition_by (fun (idc,_) (idc',_) -> idc = idc') l in
  let l = List.map (List.map snd) l in
  List.map (fun l -> try List.assoc true l with Not_found -> snd (List.hd l)) l

(* We try to instantiate the evar assuming the body won't depend
 * on arguments that are not Rels or Vars, or appearing several times
 * (i.e. we tackle only Miller-Pfenning patterns unification) 
 *
 * 1) Let "env |- ?ev[hyps:=args] = rhs" be the unification problem
 * 2) We limit it to a patterns unification problem "env |- ev[subst] = rhs"
 *    where only Rel's and Var's are relevant in subst
 * 3) We recur on rhs, "imitating" the term, and failing if some Rel/Var is 
 *    not in the scope of ?ev. For instance, the problem
 *    "y:nat |- ?x[] = y" where "|- ?1:nat" is not satisfiable because
 *    ?1 would be instantiated by y which is not in the scope of ?1.
 * 4) We try to "project" the term if the process of imitation fails
 *    and that only one projection is possible
 *
 * Note: we don't assume rhs in normal form, it may fail while it would
 * have succeeded after some reductions
 *)

(* Note: error_not_clean should not be an error: it simply means that the
 * conversion test that leads to the faulty call to [real_clean] should return
 * false. The problem is that we won't get the right error message.
 *)

exception NotClean of constr

let rec real_clean env isevars ev subst rhs =
  let evd = ref isevars in
  let rec subs rigid k t =
    match kind_of_term t with
      | Rel i ->
 	 if i<=k then t
 	 else
	   (* Flex/Rel problem: unifiable iff Rel projectable from ev subst *)
	   project rigid env evd (mkRel (i-k)) subst
      | Evar (ev,args) ->
          if Evd.is_defined_evar !evd (ev,args) then
            subs rigid k (existential_value (evars_of !evd) (ev,args))
          else
	    (* Flex/Flex problem: restriction to a common scope *)
	    let args' = Array.map (subs false k) args in
	    if need_restriction k args' then
              do_restrict_hyps (reset_context env) k evd ev args'
	    else
	      mkEvar (ev,args')
      | Var id ->
	  (* Flex/Var problem: unifiable iff Var projectable from ev subst *)
	  project rigid env evd t subst
      | _ ->
	  (* Flex/Rigid problem (or assimilated if not normal): we "imitate" *)
	  map_constr_with_binders succ (subs rigid) k t
  in
  let rhs = nf_evar (evars_of isevars) rhs in
  let rhs = whd_beta rhs (* heuristic *) in
  let body = 
    try subs true 0 rhs
    with NotClean t -> 
      error_not_clean env (evars_of !evd) ev t (evar_source ev !evd) in
  (!evd,body)

(* Assume a set of solutions to the following two kinds of problems:
 *
 * - ?n[...;x:=y;...] = y
 * - ?n[...;x:=?m[args];...] = y with ?m[args] = y recursively solvable
 *   
 * If the set of solutions is a singleton, [project_variable] instantiates
 * the auxiliary evars (?m etc) and return the instance of ?n=x. It
 * also instantiates the type of [?m] if this type is an evar.
 *
 * (see test-suite/success/Fixpoint.v for an example of application of
 * the second kind of problem).
 *)

and project rigid env isevars t subst =
  let rec aux = function
  | [] -> raise Not_found
  | (id,_)::_::_ ->
      if rigid then raise Not_found else (* Irreversible choice *) mkVar id
  | [id,ProjectVar] -> mkVar id
  | [id,ProjectEvar ((ev,argsv),evi,sols)] ->
      isevars := Evd.evar_define ev (aux sols) !isevars;
      let ty = Retyping.get_type_of env (evars_of !isevars) t in
      let ty = whd_betadeltaiota env (evars_of !isevars) ty in
      if not (isSort ty) & isEvar evi.evar_concl then
	begin
	  (* Don't try to instantiate if a sort because if evar_concl is an
             evar it may commit to a univ level which is not the right
             one (however, regarding coercions, because t is obtained by
             unif, we know that no coercion can be inserted) *)
	  let subst = make_pure_subst evi argsv in
	  let ty' = replace_vars subst evi.evar_concl in
	  isevars := fst (evar_define env (destEvar ty') ty !isevars)
	end;
      mkVar id in
  try aux (List.rev (find_projectable_vars env (evars_of !isevars) t subst))
  with Not_found -> if not rigid then t else raise (NotClean t)

(* [evar_define] solves the problem "?ev[args] = rhs" when "?ev" is an 
 * uninstantiated such that "hyps |- ?ev : typ". Otherwise said,
 * [evar_define] tries to find an instance lhs such that
 * "lhs [ hyps \ args ]" unifies to rhs. The term "lhs" must be closed in
 * context "hyps" and not referring to itself.
 *)

(* env needed for error messages... *)
and evar_define env (ev,argsv) rhs isevars =
  if occur_evar ev rhs
  then error_occur_check env (evars_of isevars) ev rhs;
  let evi = Evd.find (evars_of isevars) ev in
  (* the bindings to invert *)
  let subst = make_projectable_subst (evars_of isevars) evi argsv in
  let (isevars',body) = real_clean env isevars ev subst rhs in
  if occur_meta body then error "Meta cannot occur in evar body"
  else
    (* needed only if an inferred type *)
    let body = refresh_universes body in
(* Cannot strictly type instantiations since the unification algorithm
 * does not unify applications from left to right.
 * e.g problem f x == g y yields x==y and f==g (in that order) 
 * Another problem is that type variables are evars of type Type
   let _ =
      try
        let env = evar_env evi in
        let ty = evi.evar_concl in
        Typing.check env (evars_of isevars') body ty
      with e ->
        pperrnl
          (str "Ill-typed evar instantiation: " ++ fnl() ++
           pr_evar_defs isevars' ++ fnl() ++
           str "----> " ++ int ev ++ str " := " ++
           print_constr body);
        raise e in*)
    let isevars'' = Evd.evar_define ev body isevars' in
    isevars'',[ev]



(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_evars isevars t = 
  try let _ = local_strong (whd_ise (evars_of isevars)) t in false
  with Uninstantiated_evar _ -> true

let is_ground_term isevars t =
  not (has_undefined_evars isevars t)

let head_is_evar isevars = 
  let rec hrec k = match kind_of_term k with
    | Evar n   -> not (Evd.is_defined_evar isevars n)
    | App (f,_) -> hrec f
    | Cast (c,_,_) -> hrec c
    | _ -> false
  in 
  hrec 

let rec is_eliminator c = match kind_of_term c with
  | App _    -> true
  | Case _ -> true
  | Cast (c,_,_) -> is_eliminator c
  | _ -> false

let head_is_embedded_evar isevars c =
  (head_is_evar isevars c) & (is_eliminator c)

let head_evar = 
  let rec hrec c = match kind_of_term c with
    | Evar (ev,_)       -> ev
    | Case (_,_,c,_) -> hrec c
    | App (c,_)        -> hrec c
    | Cast (c,_,_)        -> hrec c
    | _                   -> failwith "headconstant"
  in 
  hrec 

(* Check if an applied evar "?X[args] l" is a Miller's pattern; note
   that we don't care whether args itself contains Rel's or even Rel's
   distinct from the ones in l *)

let is_unification_pattern_evar (_,args) l =
  let l' = Array.to_list args @ l in
  List.for_all (fun a -> isRel a or isVar a) l' & list_distinct l'

let is_unification_pattern f l =
  match kind_of_term f with
    | Meta _ -> array_for_all isRel l & array_distinct l
    | Evar ev -> is_unification_pattern_evar ev (Array.to_list l)
    | _ -> false

(* From a unification problem "?X l1 = term1 l2" such that l1 is made
   of distinct rel's, build "\x1...xn.(term1 l2)" (patterns unification) *)

let solve_pattern_eqn env l1 c =
  let c' = List.fold_right (fun a c ->
    let c' = subst_term (lift 1 a) (lift 1 c) in
    match kind_of_term a with
      (* Rem: if [a] links to a let-in, do as if it were an assumption *)
      | Rel n -> let (na,_,t) = lookup_rel n env in mkLambda (na,lift n t,c')
      | Var id -> let (id,_,t) = lookup_named id env in mkNamedLambda id t c'
      | _ -> assert false) 
    l1 c in
  whd_eta c'

(* This code (i.e. solve_pb, etc.) takes a unification
 * problem, and tries to solve it. If it solves it, then it removes
 * all the conversion problems, and re-runs conversion on each one, in
 * the hopes that the new solution will aid in solving them.
 *
 * The kinds of problems it knows how to solve are those in which
 * the usable arguments of an existential var are all themselves
 * universal variables.
 * The solution to this problem is to do renaming for the Var's,
 * to make them match up with the Var's which are found in the
 * hyps of the existential, to do a "pop" for each Rel which is
 * not an argument of the existential, and a subst1 for each which
 * is, again, with the corresponding variable. This is done by
 * evar_define
 *
 * Thus, we take the arguments of the existential which we are about
 * to assign, and zip them with the identifiers in the hypotheses.
 * Then, we process all the Var's in the arguments, and sort the
 * Rel's into ascending order.  Then, we just march up, doing
 * subst1's and pop's.
 *
 * NOTE: We can do this more efficiently for the relative arguments,
 * by building a long substituend by hand, but this is a pain in the
 * ass.
 *)

let status_changed lev (pbty,_,t1,t2) =
  try 
    List.mem (head_evar t1) lev or List.mem (head_evar t2) lev
  with Failure _ ->
    try List.mem (head_evar t2) lev with Failure _ -> false

(* Solve pbs (?i x1..xn) = (?i y1..yn) which arises often in fixpoint
 * definitions. We try to unify the xi with the yi pairwise. The pairs
 * that don't unify are discarded (i.e. ?i is redefined so that it does not
 * depend on these args). *)

let solve_refl conv_algo env isevars ev argsv1 argsv2 =
  if argsv1 = argsv2 then (isevars,[]) else
  let evd = Evd.find (evars_of isevars) ev in
  let hyps = evar_context evd in
  let (isevars',_,rsign) = 
    array_fold_left2
      (fun (isevars,sgn,rsgn) a1 a2 ->
        let (isevars',b) = conv_algo env isevars Reduction.CONV a1 a2 in
	 if b then 
	   (isevars',List.tl sgn, add_named_decl (List.hd sgn) rsgn)
	 else 
	   (isevars,List.tl  sgn, rsgn))
      (isevars,hyps,[]) argsv1 argsv2 
  in
  let nsign = List.rev rsign in
  let (evd',newev) =
    let env =
      Sign.fold_named_context push_named nsign ~init:(reset_context env) in
    new_evar isevars env ~src:(evar_source ev isevars) evd.evar_concl in
  let evd'' = Evd.evar_define ev newev evd' in
  evd'', [ev]


(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstantiated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo env isevars (pbty,(n1,args1 as ev1),t2) =
  try
    let t2 = nf_evar (evars_of isevars) t2 in
    let (isevars,lsp) = match kind_of_term t2 with
      | Evar (n2,args2 as ev2) ->
	  if n1 = n2 then
	    solve_refl conv_algo env isevars n1 args1 args2
	  else
            (try evar_define env ev1 t2 isevars
            with e when precatchable_exception e ->
              evar_define env ev2 (mkEvar ev1) isevars)
(*	    if Array.length args1 < Array.length args2 then
	      evar_define env ev2 (mkEvar ev1) isevars
	    else 
	      evar_define env ev1 t2 isevars*)
      | _ ->
	  evar_define env ev1 t2 isevars in
    let (isevars,pbs) = get_conv_pbs isevars (status_changed lsp) in
    List.fold_left
      (fun (isevars,b as p) (pbty,env,t1,t2) ->
	if b then conv_algo env isevars pbty t1 t2 else p) (isevars,true)
      pbs
  with e when precatchable_exception e ->
    (isevars,false)


(* [check_evars] fails if some unresolved evar remains *)
(* it assumes that the defined existentials have already been substituted *)

let check_evars env initial_sigma isevars c =
  let sigma = evars_of isevars in
  let c = nf_evar sigma c in
  let rec proc_rec c =
    match kind_of_term c with
      | Evar (ev,args) ->
          assert (Evd.mem sigma ev);
	  if not (Evd.mem initial_sigma ev) then
            let (loc,k) = evar_source ev isevars in
	    error_unsolvable_implicit loc env sigma k
      | _ -> iter_constr proc_rec c
  in proc_rec c

(* Operations on value/type constraints *)

type type_constraint_type = (int * int) option * constr
type type_constraint = type_constraint_type option

type val_constraint = constr option

(* Old comment...
 * Basically, we have the following kind of constraints (in increasing
 * strength order):
 *   (false,(None,None)) -> no constraint at all
 *   (true,(None,None))  -> we must build a judgement which _TYPE is a kind
 *   (_,(None,Some ty))  -> we must build a judgement which _TYPE is ty
 *   (_,(Some v,_))      -> we must build a judgement which _VAL is v
 * Maybe a concrete datatype would be easier to understand.
 * We differentiate (true,(None,None)) from (_,(None,Some Type))
 * because otherwise Case(s) would be misled, as in
 * (n:nat) Case n of bool [_]nat end  would infer the predicate Type instead
 * of Set.
 *)

(* The empty type constraint *)
let empty_tycon = None

let mk_tycon_type c = (None, c)
let mk_abstr_tycon_type n c = (Some (n, n), c) (* First component is initial abstraction, second
						  is current abstraction *)

(* Builds a type constraint *)
let mk_tycon ty = Some (mk_tycon_type ty)

let mk_abstr_tycon n ty = Some (mk_abstr_tycon_type n ty)

(* Constrains the value of a type *)
let empty_valcon = None

(* Builds a value constraint *)
let mk_valcon c = Some c

(* Refining an evar to a product or a sort *)

(* Declaring any type to be in the sort Type shouldn't be harmful since
   cumulativity now includes Prop and Set in Type...
   It is, but that's not too bad *)
let define_evar_as_abstraction abs evd (ev,args) =
  let evi = Evd.find (evars_of evd) ev in
  let evenv = evar_env evi in
  let (evd1,dom) = new_evar evd evenv (new_Type()) in
  let nvar =
    next_ident_away (id_of_string "x")
      (ids_of_named_context (evar_context evi)) in
  let newenv = push_named (nvar, None, dom) evenv in
  let (evd2,rng) =
    new_evar evd1 newenv ~src:(evar_source ev evd1) (new_Type()) in
  let prod = abs (Name nvar, dom, subst_var nvar rng) in
  let evd3 = Evd.evar_define ev prod evd2 in
  let evdom = fst (destEvar dom), args in
  let evrng =
    fst (destEvar rng), array_cons (mkRel 1) (Array.map (lift 1) args) in
  let prod' = abs (Name nvar, mkEvar evdom, mkEvar evrng) in
  (evd3,prod')

let define_evar_as_arrow evd (ev,args) =
  define_evar_as_abstraction (fun t -> mkProd t) evd (ev,args)

let define_evar_as_lambda evd (ev,args) =
  define_evar_as_abstraction (fun t -> mkLambda t) evd (ev,args)

let define_evar_as_sort isevars (ev,args) =
  let s = new_Type () in
  Evd.evar_define ev s isevars, destSort s


(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type () = Typeops.judge_of_type (new_univ ())

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env isevars tycon = 
  let rec real_split c = 
    let sigma = evars_of isevars in
    let t = whd_betadeltaiota env sigma c in
      match kind_of_term t with
	| Prod (na,dom,rng) -> isevars, (na, dom, rng)
	| Evar ev when not (Evd.is_defined_evar isevars ev) ->
	    let (isevars',prod) = define_evar_as_arrow isevars ev in
	    let (_,dom,rng) = destProd prod in
	      isevars',(Anonymous, dom, rng)
	| _ -> error_not_product_loc loc env sigma c
  in
    match tycon with
      | None -> isevars,(Anonymous,None,None)
      | Some (abs, c) ->
	  (match abs with
	       None -> 
		 let isevars', (n, dom, rng) = real_split c in
		   isevars', (n, mk_tycon dom, mk_tycon rng)
	     | Some (init, cur) ->
		 if cur = 0 then 
		   let isevars', (x, dom, rng) = real_split c in
		     isevars, (Anonymous, 
			       Some (Some (init, 0), dom), 
			       Some (Some (init, 0), rng))
		 else
		   isevars, (Anonymous, None, Some (Some (init, pred cur), c)))

let valcon_of_tycon x = 
  match x with
    | Some (None, t) -> Some t
    | _ -> None
	
let lift_abstr_tycon_type n (abs, t) =
  match abs with 
      None -> raise (Invalid_argument "lift_abstr_tycon_type: not an abstraction")
    | Some (init, abs) ->
	let abs' = abs + n in 
	  if abs' < 0 then raise (Invalid_argument "lift_abstr_tycon_type")
	  else (Some (init, abs'), t)

let lift_tycon_type n (abs, t) = (abs, lift n t)
let lift_tycon n = option_map (lift_tycon_type n)

let pr_tycon_type env (abs, t) =
  match abs with 
      None -> Termops.print_constr_env env t
    | Some (init, cur) -> str "Abstract (" ++ int init ++ str ","  ++ int cur ++ str ") " ++ Termops.print_constr_env env t
	
let pr_tycon env = function
    None -> str "None"
  | Some t -> pr_tycon_type env t

