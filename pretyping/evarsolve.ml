(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Errors
open Names
open Term
open Vars
open Context
open Environ
open Termops
open Evd
open Namegen
open Retyping
open Reductionops
open Evarutil
open Pretype_errors

let normalize_evar evd ev =
  match kind_of_term (whd_evar evd (mkEvar ev)) with
  | Evar (evk,args) -> (evk,args)
  | _ -> assert false

let get_polymorphic_positions f = 
  let open Declarations in
  match kind_of_term f with
  | Ind (ind, u) | Construct ((ind, _), u) -> 
    let mib,oib = Global.lookup_inductive ind in
      (match oib.mind_arity with
      | RegularArity _ -> assert false
      | TemplateArity templ -> templ.template_param_levels)
  | Const (cst, u) ->
    let cb = Global.lookup_constant cst in
      (match cb.const_type with
      | RegularArity _ -> assert false
      | TemplateArity (_, templ) -> 
        templ.template_param_levels)
  | _ -> assert false

(**
   forall A (l : list A) -> typeof A = Type i <= Datatypes.j -> i not refreshed
   hd ?A (l : list t) -> A = t

*)
let refresh_universes ?(inferred=false) ?(onlyalg=false) pbty env evd t =
  let evdref = ref evd in
  let modified = ref false in
  let rec refresh dir t = 
    match kind_of_term t with
    | Sort (Type u as s) when
      (match Univ.universe_level u with
      | None -> true 
      | Some l -> not onlyalg && Option.is_empty (Evd.is_sort_variable evd s)) ->
    let status = if inferred then Evd.univ_flexible_alg else Evd.univ_flexible in
    let s' = evd_comb0 (new_sort_variable status) evdref in
    let evd = 
      if dir then set_leq_sort env !evdref s' s
      else set_leq_sort env !evdref s s'
    in
      modified := true; evdref := evd; mkSort s'
    | Prod (na,u,v) -> 
    mkProd (na,u,refresh dir v)
    | _ -> t
  (** Refresh the types of evars under template polymorphic references *)
  and refresh_term_evars onevars t =
    match kind_of_term t with
    | App (f, args) when is_template_polymorphic env f ->
      let pos = get_polymorphic_positions f in
	refresh_polymorphic_positions args pos
    | Evar (ev, a) when onevars ->
      let evi = Evd.find !evdref ev in
      let ty' = refresh true evi.evar_concl in
	if !modified then 
	  evdref := Evd.add !evdref ev {evi with evar_concl = ty'}
	else ()
    | _ -> iter_constr (refresh_term_evars onevars) t
  and refresh_polymorphic_positions args pos =
    let rec aux i = function
      | Some l :: ls -> 
        if i < Array.length args then 
	  ignore(refresh_term_evars true args.(i));
        aux (succ i) ls
      | None :: ls -> 
        if i < Array.length args then 
          ignore(refresh_term_evars false args.(i));
	aux (succ i) ls
      | [] -> ()
    in aux 0 pos
  in
  let t' = 
    if isArity t then
      (match pbty with
      | None -> t
      | Some dir -> refresh dir t)
    else (refresh_term_evars false t; t)
  in
    if !modified then !evdref, t' else !evdref, t

let get_type_of_refresh ?(polyprop=true) ?(lax=false) env sigma c =
  let ty = Retyping.get_type_of ~polyprop ~lax env sigma c in
    refresh_universes (Some false) env sigma ty

(************************)
(* Unification results  *)
(************************)

type unification_result =
  | Success of evar_map
  | UnifFailure of evar_map * unification_error

let is_success = function Success _ -> true | UnifFailure _ -> false

let test_success conv_algo env evd c c' rhs =
  is_success (conv_algo env evd c c' rhs)

let add_conv_oriented_pb (pbty,env,t1,t2) evd =
  match pbty with
  | Some true -> add_conv_pb (Reduction.CUMUL,env,t1,t2) evd
  | Some false -> add_conv_pb (Reduction.CUMUL,env,t2,t1) evd
  | None -> add_conv_pb (Reduction.CONV,env,t1,t2) evd

(*------------------------------------*
 * Restricting existing evars         *
 *------------------------------------*)

type 'a update =
| UpdateWith of 'a
| NoUpdate

let inst_of_vars sign = Array.map_of_list (fun (id,_,_) -> mkVar id) sign

let restrict_evar_key evd evk filter candidates =
  match filter, candidates with
  | None, NoUpdate -> evd, evk
  | _ ->
    let evi = Evd.find_undefined evd evk in
    let oldfilter = evar_filter evi in
    begin match filter, candidates with
    | Some filter, NoUpdate when Filter.equal oldfilter filter ->
      evd, evk
    | _ ->
      let filter = match filter with
      | None -> evar_filter evi
      | Some filter -> filter in
      let candidates = match candidates with
      | NoUpdate -> evi.evar_candidates
      | UpdateWith c -> Some c in
      restrict_evar evd evk filter candidates
    end

(* Restrict an applied evar and returns its restriction in the same context *)
let restrict_applied_evar evd (evk,argsv) filter candidates =
  let evd,newevk = restrict_evar_key evd evk filter candidates in
  let newargsv = match filter with
  | None -> (* optim *) argsv
  | Some filter ->
      let evi = Evd.find evd evk in
      let subfilter = Filter.compose (evar_filter evi) filter in
      Filter.filter_array subfilter argsv in
  evd,(newevk,newargsv)

(* Restrict an evar in the current evar_map *)
let restrict_evar evd evk filter candidates =
  fst (restrict_evar_key evd evk filter candidates)

(* Restrict an evar in the current evar_map *)
let restrict_instance evd evk filter argsv =
  match filter with None -> argsv | Some filter ->
  let evi = Evd.find evd evk in
  Filter.filter_array (Filter.compose (evar_filter evi) filter) argsv

let noccur_evar env evd evk c =
  let rec occur_rec k c = match kind_of_term c with
  | Evar (evk',args' as ev') ->
      (match safe_evar_value evd ev' with
       | Some c -> occur_rec k c
       | None ->
           if Evar.equal evk evk' then raise Occur
           else Array.iter (occur_rec k) args')
  | Rel i when i > k ->
      (match pi2 (Environ.lookup_rel (i-k) env) with
       | None -> ()
       | Some b -> occur_rec k (lift i b))
  | _ -> iter_constr_with_binders succ occur_rec k c
  in
  try occur_rec 0 c; true with Occur -> false

(***************************************)
(* Managing chains of local definitons *)
(***************************************)

(* Expand rels and vars that are bound to other rels or vars so that
   dependencies in variables are canonically associated to the most ancient
   variable in its family of aliased variables *)

let compute_var_aliases sign =
  List.fold_right (fun (id,b,c) aliases ->
    match b with
    | Some t ->
        (match kind_of_term t with
        | Var id' ->
            let aliases_of_id =
              try Id.Map.find id' aliases with Not_found -> [] in
            Id.Map.add id (aliases_of_id@[t]) aliases
        | _ ->
            Id.Map.add id [t] aliases)
    | None -> aliases)
    sign Id.Map.empty

let compute_rel_aliases var_aliases rels =
  snd (List.fold_right (fun (_,b,t) (n,aliases) ->
    (n-1,
     match b with
     | Some t ->
         (match kind_of_term t with
         | Var id' ->
             let aliases_of_n =
               try Id.Map.find id' var_aliases with Not_found -> [] in
             Int.Map.add n (aliases_of_n@[t]) aliases
         | Rel p ->
             let aliases_of_n =
               try Int.Map.find (p+n) aliases with Not_found -> [] in
             Int.Map.add n (aliases_of_n@[mkRel (p+n)]) aliases
         | _ ->
             Int.Map.add n [lift n t] aliases)
     | None -> aliases))
         rels (List.length rels,Int.Map.empty))

let make_alias_map env =
  (* We compute the chain of aliases for each var and rel *)
  let var_aliases = compute_var_aliases (named_context env) in
  let rel_aliases = compute_rel_aliases var_aliases (rel_context env) in
  (var_aliases,rel_aliases)

let lift_aliases n (var_aliases,rel_aliases as aliases) =
  if Int.equal n 0 then aliases else
  (var_aliases,
   Int.Map.fold (fun p l -> Int.Map.add (p+n) (List.map (lift n) l))
     rel_aliases Int.Map.empty)

let get_alias_chain_of aliases x = match kind_of_term x with
  | Rel n -> (try Int.Map.find n (snd aliases) with Not_found -> [])
  | Var id -> (try Id.Map.find id (fst aliases) with Not_found -> [])
  | _ -> []

let normalize_alias_opt aliases x =
  match get_alias_chain_of aliases x with
  | []  -> None
  | a::_ when isRel a || isVar a -> Some a
  | [_] -> None
  | _::a::_ -> Some a

let normalize_alias aliases x =
  match normalize_alias_opt aliases x with
  | Some a -> a
  | None -> x

let normalize_alias_var var_aliases id =
  destVar (normalize_alias (var_aliases,Int.Map.empty) (mkVar id))

let extend_alias (_,b,_) (var_aliases,rel_aliases) =
  let rel_aliases =
    Int.Map.fold (fun n l -> Int.Map.add (n+1) (List.map (lift 1) l))
      rel_aliases Int.Map.empty in
  let rel_aliases =
    match b with
    | Some t ->
        (match kind_of_term t with
        | Var id' ->
            let aliases_of_binder =
              try Id.Map.find id' var_aliases with Not_found -> [] in
            Int.Map.add 1 (aliases_of_binder@[t]) rel_aliases
        | Rel p ->
            let aliases_of_binder =
              try Int.Map.find (p+1) rel_aliases with Not_found -> [] in
            Int.Map.add 1 (aliases_of_binder@[mkRel (p+1)]) rel_aliases
        | _ ->
            Int.Map.add 1 [lift 1 t] rel_aliases)
    | None -> rel_aliases in
  (var_aliases, rel_aliases)

let expand_alias_once aliases x =
  match get_alias_chain_of aliases x with
  | []  -> None
  | l -> Some (List.last l)

let expansions_of_var aliases x =
  match get_alias_chain_of aliases x with
  | [] -> [x]
  | a::_ as l when isRel a || isVar a -> x :: List.rev l
  | _::l -> x :: List.rev l

let expansion_of_var aliases x =
  match get_alias_chain_of aliases x with
  | [] -> x
  | a::_ -> a

let rec expand_vars_in_term_using aliases t = match kind_of_term t with
  | Rel _ | Var _ ->
      normalize_alias aliases t
  | _ ->
      map_constr_with_full_binders
        extend_alias expand_vars_in_term_using aliases t

let expand_vars_in_term env = expand_vars_in_term_using (make_alias_map env)

let free_vars_and_rels_up_alias_expansion aliases c =
  let acc1 = ref Int.Set.empty and acc2 = ref Id.Set.empty in
  let cache_rel = ref Int.Set.empty and cache_var = ref Id.Set.empty in
  let is_in_cache depth = function
    | Rel n -> Int.Set.mem (n-depth) !cache_rel
    | Var s -> Id.Set.mem s !cache_var
    | _ -> false in
  let put_in_cache depth = function
    | Rel n -> cache_rel := Int.Set.add (n-depth) !cache_rel
    | Var s -> cache_var := Id.Set.add s !cache_var
    | _ -> () in
  let rec frec (aliases,depth) c =
    match kind_of_term c with
    | Rel _ | Var _ as ck ->
      if is_in_cache depth ck then () else begin
      put_in_cache depth ck;
      let c = expansion_of_var aliases c in
        match kind_of_term c with
        | Var id -> acc2 := Id.Set.add id !acc2
        | Rel n -> if n >= depth+1 then acc1 := Int.Set.add (n-depth) !acc1
        | _ -> frec (aliases,depth) c end
    | Const _ | Ind _ | Construct _ ->
        acc2 := Id.Set.union (vars_of_global (Global.env()) c) !acc2
    | _ ->
        iter_constr_with_full_binders
          (fun d (aliases,depth) -> (extend_alias d aliases,depth+1))
          frec (aliases,depth) c
  in
  frec (aliases,0) c;
  (!acc1,!acc2)

(********************************)
(* Managing pattern-unification *)
(********************************)

let rec expand_and_check_vars aliases = function
  | [] -> []
  | a::l when isRel a || isVar a ->
      let a = expansion_of_var aliases a in
      if isRel a || isVar a then a :: expand_and_check_vars aliases l
      else raise Exit
  | _ ->
      raise Exit

module Constrhash = Hashtbl.Make
  (struct type t = constr
          let equal = Term.eq_constr
          let hash = hash_constr
   end)

let constr_list_distinct l =
  let visited = Constrhash.create 23 in
  let rec loop = function
    | h::t ->
        if Constrhash.mem visited h then false
        else (Constrhash.add visited h h; loop t)
    | [] -> true
  in loop l

let get_actual_deps aliases l t =
  if occur_meta_or_existential t then
    (* Probably no restrictions on allowed vars in presence of evars *)
    l
  else
    (* Probably strong restrictions coming from t being evar-closed *)
    let (fv_rels,fv_ids) = free_vars_and_rels_up_alias_expansion aliases t in
    List.filter (fun c ->
      match kind_of_term c with
      | Var id -> Id.Set.mem id fv_ids
      | Rel n -> Int.Set.mem n fv_rels
      | _ -> assert false) l

let remove_instance_local_defs evd evk args =
  let evi = Evd.find evd evk in
  let len = Array.length args in
  let rec aux sign i = match sign with
  | [] ->
    let () = assert (i = len) in []
  | (_, None, _) :: sign ->
    let () = assert (i < len) in
    (Array.unsafe_get args i) :: aux sign (succ i)
  | (_, Some _, _) :: sign ->
    aux sign (succ i)
  in
  aux (evar_filtered_context evi) 0

(* Check if an applied evar "?X[args] l" is a Miller's pattern *)

let find_unification_pattern_args env l t =
  if List.for_all (fun x -> isRel x || isVar x) l (* common failure case *) then
    let aliases = make_alias_map env in
    match (try Some (expand_and_check_vars aliases l) with Exit -> None) with
    | Some l as x when constr_list_distinct (get_actual_deps aliases l t) -> x
    | _ -> None
  else
    None

let is_unification_pattern_meta env nb m l t =
  (* Variables from context and rels > nb are implicitly all there *)
  (* so we need to be a rel <= nb *)
  if List.for_all (fun x -> isRel x && destRel x <= nb) l then
    match find_unification_pattern_args env l t with
    | Some _ as x when not (dependent (mkMeta m) t) -> x
    | _ -> None
  else
    None

let is_unification_pattern_evar env evd (evk,args) l t =
  if List.for_all (fun x -> isRel x || isVar x) l 
    && noccur_evar env evd evk t
  then
    let args = remove_instance_local_defs evd evk args in
    let n = List.length args in
      match find_unification_pattern_args env (args @ l) t with
      | Some l -> Some (List.skipn n l)
      | _ -> None
  else None

let is_unification_pattern_pure_evar env evd (evk,args) t =
  let is_ev = is_unification_pattern_evar env evd (evk,args) [] t in
  match is_ev with
  | None -> false
  | Some _ -> true

let is_unification_pattern (env,nb) evd f l t =
  match kind_of_term f with
  | Meta m -> is_unification_pattern_meta env nb m l t
  | Evar ev -> is_unification_pattern_evar env evd ev l t
  | _ -> None

(* From a unification problem "?X l = c", build "\x1...xn.(term1 l2)"
   (pattern unification). It is assumed that l is made of rel's that
   are distinct and not bound to aliases. *)
(* It is also assumed that c does not contain metas because metas
   *implicitly* depend on Vars but lambda abstraction will not reflect this
   dependency: ?X x = ?1 (?1 is a meta) will return \_.?1 while it should
   return \y. ?1{x\y} (non constant function if ?1 depends on x) (BB) *)
let solve_pattern_eqn env l c =
  let c' = List.fold_right (fun a c ->
    let c' = subst_term (lift 1 a) (lift 1 c) in
    match kind_of_term a with
      (* Rem: if [a] links to a let-in, do as if it were an assumption *)
      | Rel n ->
          let d = map_rel_declaration (lift n) (lookup_rel n env) in
          mkLambda_or_LetIn d c'
      | Var id ->
          let d = lookup_named id env in mkNamedLambda_or_LetIn d c'
      | _ -> assert false)
    l c in
  (* Warning: we may miss some opportunity to eta-reduce more since c'
     is not in normal form *)
  whd_eta c'

(*****************************************)
(* Refining/solving unification problems *)
(*****************************************)

(* Knowing that [Gamma |- ev : T] and that [ev] is applied to [args],
 * [make_projectable_subst ev args] builds the substitution [Gamma:=args].
 * If a variable and an alias of it are bound to the same instance, we skip
 * the alias (we just use eq_constr -- instead of conv --, since anyway,
 * only instances that are variables -- or evars -- are later considered;
 * morever, we can bet that similar instances came at some time from
 * the very same substitution. The removal of aliased duplicates is
 * useful to ensure the uniqueness of a projection.
*)

let make_projectable_subst aliases sigma evi args =
  let sign = evar_filtered_context evi in
  let evar_aliases = compute_var_aliases sign in
  let (_,full_subst,cstr_subst) =
    List.fold_right
      (fun (id,b,c) (args,all,cstrs) ->
        match b,args with
        | None, a::rest ->
            let a = whd_evar sigma a in
            let cstrs =
              let a',args = decompose_app_vect a in
              match kind_of_term a' with
              | Construct cstr ->
                  let l = try Constrmap.find (fst cstr) cstrs with Not_found -> [] in
                  Constrmap.add (fst cstr) ((args,id)::l) cstrs
              | _ -> cstrs in
            (rest,Id.Map.add id [a,normalize_alias_opt aliases a,id] all,cstrs)
        | Some c, a::rest ->
            let a = whd_evar sigma a in
            (match kind_of_term c with
            | Var id' ->
                let idc = normalize_alias_var evar_aliases id' in
                let sub = try Id.Map.find idc all with Not_found -> [] in
                if List.exists (fun (c,_,_) -> Term.eq_constr a c) sub then
                  (rest,all,cstrs)
                else
                  (rest,
                   Id.Map.add idc ((a,normalize_alias_opt aliases a,id)::sub) all,
                   cstrs)
            | _ ->
                (rest,Id.Map.add id [a,normalize_alias_opt aliases a,id] all,cstrs))
        | _ -> anomaly (Pp.str "Instance does not match its signature"))
      sign (Array.rev_to_list args,Id.Map.empty,Constrmap.empty) in
  (full_subst,cstr_subst)

(*------------------------------------*
 * operations on the evar constraints *
 *------------------------------------*)

(* We have a unification problem Σ; Γ |- ?e[u1..uq] = t : s where ?e is not yet
 * declared in Σ but yet known to be declarable in some context x1:T1..xq:Tq.
 * [define_evar_from_virtual_equation ... Γ Σ t (x1:T1..xq:Tq) .. (u1..uq) (x1..xq)]
 * declares x1:T1..xq:Tq |- ?e : s such that ?e[u1..uq] = t holds.
 *)

let define_evar_from_virtual_equation define_fun env evd src t_in_env ty_t_in_sign sign filter inst_in_env =
  let evd,evar_in_env = new_evar_instance sign evd ty_t_in_sign ~filter ~src inst_in_env in
  let t_in_env = whd_evar evd t_in_env in
  let evd = define_fun env evd None (destEvar evar_in_env) t_in_env in
  let ctxt = named_context_of_val sign in
  let inst_in_sign = inst_of_vars (Filter.filter_list filter ctxt) in
  let evar_in_sign = mkEvar (fst (destEvar evar_in_env), inst_in_sign) in
  (evd,whd_evar evd evar_in_sign)

(* We have x1..xq |- ?e1 : τ and had to solve something like
 * Σ; Γ |- ?e1[u1..uq] = (...\y1 ... \yk ... c), where c is typically some
 * ?e2[v1..vn], hence flexible. We had to go through k binders and now
 * virtually have x1..xq, y1'..yk' | ?e1' : τ' and the equation
 * Γ, y1..yk |- ?e1'[u1..uq y1..yk] = c.
 * [materialize_evar Γ evd k (?e1[u1..uq]) τ'] extends Σ with the declaration
 * of ?e1' and returns both its instance ?e1'[x1..xq y1..yk] in an extension
 * of the context of e1 so that e1 can be instantiated by
 * (...\y1' ... \yk' ... ?e1'[x1..xq y1'..yk']),
 * and the instance ?e1'[u1..uq y1..yk] so that the remaining equation
 * ?e1'[u1..uq y1..yk] = c can be registered
 *
 * Note that, because invert_definition does not check types, we need to
 * guess the types of y1'..yn' by inverting the types of y1..yn along the
 * substitution u1..uq.
 *)

let materialize_evar define_fun env evd k (evk1,args1) ty_in_env =
  let evi1 = Evd.find_undefined evd evk1 in
  let env1,rel_sign = env_rel_context_chop k env in
  let sign1 = evar_hyps evi1 in
  let filter1 = evar_filter evi1 in
  let src = subterm_source evk1 evi1.evar_source in
  let ids1 = List.map pi1 (named_context_of_val sign1) in
  let inst_in_sign = List.map mkVar (Filter.filter_list filter1 ids1) in
  let (sign2,filter2,inst2_in_env,inst2_in_sign,_,evd,_) =
    List.fold_right (fun (na,b,t_in_env as d) (sign,filter,inst_in_env,inst_in_sign,env,evd,avoid) ->
      let id = next_name_away na avoid in
      let evd,t_in_sign =
        let s = Retyping.get_sort_of env evd t_in_env in
        let evd,ty_t_in_sign = refresh_universes ~inferred:true (Some false) env evd (mkSort s) in
        define_evar_from_virtual_equation define_fun env evd src t_in_env
          ty_t_in_sign sign filter inst_in_env in
      let evd,b_in_sign = match b with
      | None -> evd,None
      | Some b ->
          let evd,b = define_evar_from_virtual_equation define_fun env evd src b
            t_in_sign sign filter inst_in_env in
          evd,Some b in
      (push_named_context_val (id,b_in_sign,t_in_sign) sign, Filter.extend 1 filter,
       (mkRel 1)::(List.map (lift 1) inst_in_env),
       (mkRel 1)::(List.map (lift 1) inst_in_sign),
       push_rel d env,evd,id::avoid))
      rel_sign
      (sign1,filter1,Array.to_list args1,inst_in_sign,env1,evd,ids1)
  in
  let evd,ev2ty_in_sign =
    let s = Retyping.get_sort_of env evd ty_in_env in
    let evd,ty_t_in_sign = refresh_universes ~inferred:true (Some false) env evd (mkSort s) in
    define_evar_from_virtual_equation define_fun env evd src ty_in_env
      ty_t_in_sign sign2 filter2 inst2_in_env in
  let evd,ev2_in_sign =
    new_evar_instance sign2 evd ev2ty_in_sign ~filter:filter2 ~src inst2_in_sign in
  let ev2_in_env = (fst (destEvar ev2_in_sign), Array.of_list inst2_in_env) in
  (evd, ev2_in_sign, ev2_in_env)

let restrict_upon_filter evd evk p args =
  let oldfullfilter = evar_filter (Evd.find_undefined evd evk) in
  let len = Array.length args in
  Filter.restrict_upon oldfullfilter len (fun i -> p (Array.unsafe_get args i))

(***************)
(* Unification *)

(* Inverting constructors in instances (common when inferring type of match) *)

let find_projectable_constructor env evd cstr k args cstr_subst =
  try
    let l = Constrmap.find cstr cstr_subst in
    let args = Array.map (lift (-k)) args in
    let l =
      List.filter (fun (args',id) ->
        (* is_conv is maybe too strong (and source of useless computation) *)
        (* (at least expansion of aliases is needed) *)
        Array.for_all2 (is_conv env evd) args args') l in
    List.map snd l
  with Not_found ->
    []

(* [find_projectable_vars env sigma y subst] finds all vars of [subst]
 * that project on [y]. It is able to find solutions to the following
 * two kinds of problems:
 *
 * - ?n[...;x:=y;...] = y
 * - ?n[...;x:=?m[args];...] = y with ?m[args] = y recursively solvable
 *
 * (see test-suite/success/Fixpoint.v for an example of application of
 * the second kind of problem).
 *
 * The seek for [y] is up to variable aliasing.  In case of solutions that
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
 * z1; z2:=z1 |- ?ev[z1]    = z2  y1:A          y1  thanks to expand_var
 * z1; z2:=z1 |- ?ev[z2]    = z1  y1:A          y1  thanks to expand_var
 * z3         |- ?ev[z3;z3] = z3  y1:A; y2:=y1  y2  see make_projectable_subst
 *
 * Remark: [find_projectable_vars] assumes that identical instances of
 * variables in the same set of aliased variables are already removed (see
 * [make_projectable_subst])
 *)

type evar_projection =
| ProjectVar
| ProjectEvar of existential * evar_info * Id.t * evar_projection

exception NotUnique
exception NotUniqueInType of (Id.t * evar_projection) list

let rec assoc_up_to_alias sigma aliases y yc = function
  | [] -> raise Not_found
  | (c,cc,id)::l ->
      let c' = whd_evar sigma c in
      if Term.eq_constr y c' then id
      else
        match l with
        | _ :: _ -> assoc_up_to_alias sigma aliases y yc l
        | [] ->
          (* Last chance, we reason up to alias conversion *)
          match (if c == c' then cc else normalize_alias_opt aliases c') with
          | Some cc when Term.eq_constr yc cc -> id
          | _ -> if Term.eq_constr yc c then id else raise Not_found

let rec find_projectable_vars with_evars aliases sigma y subst =
  let yc = normalize_alias aliases y in
  let is_projectable idc idcl subst' =
    (* First test if some [id] aliased to [idc] is bound to [y] in [subst] *)
    try
      let id = assoc_up_to_alias sigma aliases y yc idcl in
      (id,ProjectVar)::subst'
    with Not_found ->
    (* Then test if [idc] is (indirectly) bound in [subst] to some evar *)
    (* projectable on [y] *)
      if with_evars then
        let idcl' = List.filter (fun (c,_,id) -> isEvar c) idcl in
        match idcl' with
        | [c,_,id] ->
          begin
            let (evk,argsv as t) = destEvar c in
            let evi = Evd.find sigma evk in
            let subst,_ = make_projectable_subst aliases sigma evi argsv in
            let l = find_projectable_vars with_evars aliases sigma y subst in
            match l with
            | [id',p] -> (id,ProjectEvar (t,evi,id',p))::subst'
            | _ -> subst'
          end
        | [] -> subst'
        | _ -> anomaly (Pp.str "More than one non var in aliases class of evar instance")
      else
        subst' in
  Id.Map.fold is_projectable subst []

(* [filter_solution] checks if one and only one possible projection exists
 * among a set of solutions to a projection problem *)

let filter_solution = function
  | [] -> raise Not_found
  | (id,p)::_::_ -> raise NotUnique
  | [id,p] -> (mkVar id, p)

let project_with_effects aliases sigma effects t subst =
  let c, p =
    filter_solution (find_projectable_vars false aliases sigma t subst) in
  effects := p :: !effects;
  c

let rec find_solution_type evarenv = function
  | (id,ProjectVar)::l -> pi3 (lookup_named id evarenv)
  | [id,ProjectEvar _] -> (* bugged *) pi3 (lookup_named id evarenv)
  | (id,ProjectEvar _)::l -> find_solution_type evarenv l
  | [] -> assert false

(* In case the solution to a projection problem requires the instantiation of
 * subsidiary evars, [do_projection_effects] performs them; it
 * also try to instantiate the type of those subsidiary evars if their
 * type is an evar too.
 *
 * Note: typing creates new evar problems, which induces a recursive dependency
 * with [define]. To avoid a too large set of recursive functions, we
 * pass [define] to [do_projection_effects] as a parameter.
 *)

let rec do_projection_effects define_fun env ty evd = function
  | ProjectVar -> evd
  | ProjectEvar ((evk,argsv),evi,id,p) ->
      let evd = Evd.define evk (mkVar id) evd in
      (* TODO: simplify constraints involving evk *)
      let evd = do_projection_effects define_fun env ty evd p in
      let ty = whd_betadeltaiota env evd (Lazy.force ty) in
      if not (isSort ty) then
        (* Don't try to instantiate if a sort because if evar_concl is an
           evar it may commit to a univ level which is not the right
           one (however, regarding coercions, because t is obtained by
           unif, we know that no coercion can be inserted) *)
        let subst = make_pure_subst evi argsv in
        let ty' = replace_vars subst evi.evar_concl in
        let ty' = whd_evar evd ty' in
        if isEvar ty' then define_fun env evd (Some false) (destEvar ty') ty else evd
      else
        evd

(* Assuming Σ; Γ, y1..yk |- c, [invert_arg_from_subst Γ k Σ [x1:=u1..xn:=un] c]
 * tries to return φ(x1..xn) such that equation φ(u1..un) = c is valid.
 * The strategy is to imitate the structure of c and then to invert
 * the variables of c (i.e. rels or vars of Γ) using the algorithm
 * implemented by project_with_effects/find_projectable_vars.
 * It returns either a unique solution or says whether 0 or more than
 * 1 solutions is found.
 *
 * Precondition:  Σ; Γ, y1..yk |- c /\ Σ; Γ |- u1..un
 * Postcondition: if φ(x1..xn) is returned then
 *                Σ; Γ, y1..yk |- φ(u1..un) = c /\ x1..xn |- φ(x1..xn)
 *
 * The effects correspond to evars instantiated while trying to project.
 *
 * [invert_arg_from_subst] is used on instances of evars. Since the
 * evars are flexible, these instances are potentially erasable. This
 * is why we don't investigate whether evars in the instances of evars
 * are unifiable, to the contrary of [invert_definition].
 *)

type projectibility_kind =
  | NoUniqueProjection
  | UniqueProjection of constr * evar_projection list

type projectibility_status =
  | CannotInvert
  | Invertible of projectibility_kind

let invert_arg_from_subst evd aliases k0 subst_in_env_extended_with_k_binders c_in_env_extended_with_k_binders =
  let effects = ref [] in
  let rec aux k t =
    let t = whd_evar evd t in
    match kind_of_term t with
    | Rel i when i>k0+k -> aux' k (mkRel (i-k))
    | Var id -> aux' k t
    | _ -> map_constr_with_binders succ aux k t
  and aux' k t =
    try project_with_effects aliases evd effects t subst_in_env_extended_with_k_binders
    with Not_found ->
      match expand_alias_once aliases t with
      | None -> raise Not_found
      | Some c -> aux k c in
  try
    let c = aux 0 c_in_env_extended_with_k_binders in
    Invertible (UniqueProjection (c,!effects))
  with
    | Not_found -> CannotInvert
    | NotUnique -> Invertible NoUniqueProjection

let invert_arg fullenv evd aliases k evk subst_in_env_extended_with_k_binders c_in_env_extended_with_k_binders =
  let res = invert_arg_from_subst evd aliases k subst_in_env_extended_with_k_binders c_in_env_extended_with_k_binders in
  match res with
  | Invertible (UniqueProjection (c,_)) when not (noccur_evar fullenv evd evk c)
      ->
      CannotInvert
  | _ ->
      res

exception NotEnoughInformationToInvert

let extract_unique_projection = function
| Invertible (UniqueProjection (c,_)) -> c
| _ ->
    (* For instance, there are evars with non-invertible arguments and *)
    (* we cannot arbitrarily restrict these evars before knowing if there *)
    (* will really be used; it can also be due to some argument *)
    (* (typically a rel) that is not inversible and that cannot be *)
    (* inverted either because it is needed for typing the conclusion *)
    (* of the evar to project *)
  raise NotEnoughInformationToInvert

let extract_candidates sols =
  try
    UpdateWith
      (List.map (function (id,ProjectVar) -> mkVar id | _ -> raise Exit) sols)
  with Exit ->
    NoUpdate

let invert_invertible_arg fullenv evd aliases k (evk,argsv) args' =
  let evi = Evd.find_undefined evd evk in
  let subst,_ = make_projectable_subst aliases evd evi argsv in
  let invert arg =
    let p = invert_arg fullenv evd aliases k evk subst arg in
    extract_unique_projection p
  in
  Array.map invert args'

(* Redefines an evar with a smaller context (i.e. it may depend on less
 * variables) such that c becomes closed.
 * Example: in "fun (x:?1) (y:list ?2[x]) => x = y :> ?3[x,y] /\ x = nil bool"
 * ?3 <-- ?1          no pb: env of ?3 is larger than ?1's
 * ?1 <-- list ?2     pb: ?2 may depend on x, but not ?1.
 * What we do is that ?2 is defined by a new evar ?4 whose context will be
 * a prefix of ?2's env, included in ?1's env.
 *
 * If "hyps |- ?e : T" and "filter" selects a subset hyps' of hyps then
 * [do_restrict_hyps evd ?e filter] sets ?e:=?e'[hyps'] and returns ?e'
 * such that "hyps' |- ?e : T"
 *)

let set_of_evctx l =
  List.fold_left (fun s (id,_,_) -> Id.Set.add id s) Id.Set.empty l

let filter_effective_candidates evi filter candidates =
  match filter with
  | None -> candidates
  | Some filter ->
      let ids = set_of_evctx (Filter.filter_list filter (evar_context evi)) in
      List.filter (fun a -> Id.Set.subset (collect_vars a) ids) candidates

let filter_candidates evd evk filter candidates_update =
  let evi = Evd.find_undefined evd evk in
  let candidates = match candidates_update with
  | NoUpdate -> evi.evar_candidates
  | UpdateWith c -> Some c
  in
  match candidates with
  | None -> NoUpdate
  | Some l ->
      let l' = filter_effective_candidates evi filter l in
      if List.length l = List.length l' && candidates_update = NoUpdate then
        NoUpdate
      else
        UpdateWith l'

let closure_of_filter evd evk = function
  | None -> None
  | Some filter ->
  let evi = Evd.find_undefined evd evk in
  let vars = collect_vars (Evarutil.nf_evar evd (evar_concl evi)) in
  let test b (id,c,_) = b || Idset.mem id vars || match c with None -> false | Some c -> not (isRel c || isVar c) in
  let newfilter = Filter.map_along test filter (evar_context evi) in
  if Filter.equal newfilter (evar_filter evi) then None else Some newfilter

let restrict_hyps evd evk filter candidates =
    (* What to do with dependencies?
       Assume we have x:A, y:B(x), z:C(x,y) |- ?e:T(x,y,z) and restrict on y.
       - If y is in a non-erasable position in C(x,y) (i.e. it is not below an
         occurrence of x in the hnf of C), then z should be removed too.
       - If y is in a non-erasable position in T(x,y,z) then the problem is
         unsolvable.
       Computing whether y is erasable or not may be costly and the
       interest for this early detection in practice is not obvious. We let
       it for future work. In any case, thanks to the use of filters, the whole
       (unrestricted) context remains consistent. *)
    let candidates = filter_candidates evd evk (Some filter) candidates in
    let typablefilter = closure_of_filter evd evk (Some filter) in
    (typablefilter,candidates)

exception EvarSolvedWhileRestricting of evar_map * constr

let do_restrict_hyps evd (evk,args as ev) filter candidates =
  let filter,candidates = match filter with
  | None -> None,candidates
  | Some filter -> restrict_hyps evd evk filter candidates in
  match candidates,filter with
  | UpdateWith [], _ -> error "Not solvable."
  | UpdateWith [nc],_ ->
      let evd = Evd.define evk nc evd in
      raise (EvarSolvedWhileRestricting (evd,whd_evar evd (mkEvar ev)))
  | NoUpdate, None -> evd,ev
  | _ -> restrict_applied_evar evd ev filter candidates

(* [postpone_non_unique_projection] postpones equation of the form ?e[?] = c *)
(* ?e is assumed to have no candidates *)

let postpone_non_unique_projection env evd pbty (evk,argsv as ev) sols rhs =
  let rhs = expand_vars_in_term env rhs in
  let filter =
    restrict_upon_filter evd evk
      (* Keep only variables that occur in rhs *)
      (* This is not safe: is the variable is a local def, its body *)
      (* may contain references to variables that are removed, leading to *)
      (* an ill-formed context. We would actually need a notion of filter *)
      (* that says that the body is hidden. Note that expand_vars_in_term *)
      (* expands only rels and vars aliases, not rels or vars bound to an *)
      (* arbitrary complex term *)
      (fun a -> not (isRel a || isVar a)
                || dependent a rhs || List.exists (fun (id,_) -> isVarId id a) sols)
      argsv in
  let filter = closure_of_filter evd evk filter in
  let candidates = extract_candidates sols in
  match candidates with
  | NoUpdate ->
    (* We made an approximation by not expanding a local definition *)
    let evd,ev = restrict_applied_evar evd ev filter NoUpdate in
    let pb = (pbty,env,mkEvar ev,rhs) in
    add_conv_oriented_pb pb evd
  | UpdateWith c ->
    restrict_evar evd evk filter (UpdateWith c)

(* [solve_evar_evar f Γ Σ ?e1[u1..un] ?e2[v1..vp]] applies an heuristic
 * to solve the equation Σ; Γ ⊢ ?e1[u1..un] = ?e2[v1..vp]:
 * - if there are at most one φj for each vj s.t. vj = φj(u1..un),
 *   we first restrict ?e2 to the subset v_k1..v_kq of the vj that are
 *   inversible and we set ?e1[x1..xn] := ?e2[φk1(x1..xn)..φkp(x1..xn)]
 *   (this is a case of pattern-unification)
 * - symmetrically if there are at most one ψj for each uj s.t.
 *   uj = ψj(v1..vp),
 * - otherwise, each position i s.t. ui does not occur in v1..vp has to
 *   be restricted and similarly for the vi, and we leave the equation
 *   as an open equation (performed by [postpone_evar])
 *
 * Warning: the notion of unique φj is relative to some given class
 * of unification problems
 *
 * Note: argument f is the function used to instantiate evars.
 *)

let are_canonical_instances args1 args2 env =
  let n1 = Array.length args1 in
  let n2 = Array.length args2 in
  let rec aux n = function
    | (id,_,c)::sign
        when n < n1 && isVarId id args1.(n) && isVarId id args2.(n) ->
        aux (n+1) sign
    | [] ->
        let rec aux2 n =
          Int.equal n n1 ||
          (isRelN (n1-n) args1.(n) && isRelN (n1-n) args2.(n) && aux2 (n+1))
        in aux2 n
    | _ -> false in
  Int.equal n1 n2 && aux 0 (named_context env)

let filter_compatible_candidates conv_algo env evd evi args rhs c =
  let c' = instantiate_evar_array evi c args in
  match conv_algo env evd Reduction.CONV rhs c' with
  | Success evd -> Some (c,evd)
  | UnifFailure _ -> None

(* [restrict_candidates ... filter ev1 ev2] restricts the candidates
   of ev1, removing those not compatible with the filter, as well as
   those not convertible to some candidate of ev2 *)

exception DoesNotPreserveCandidateRestriction

let restrict_candidates conv_algo env evd filter1 (evk1,argsv1) (evk2,argsv2) =
  let evi1 = Evd.find evd evk1 in
  let evi2 = Evd.find evd evk2 in
  match evi1.evar_candidates, evi2.evar_candidates with
  | _, None -> filter_candidates evd evk1 filter1 NoUpdate
  | None, Some _ -> raise DoesNotPreserveCandidateRestriction
  | Some l1, Some l2 ->
      let l1 = filter_effective_candidates evi1 filter1 l1 in
      let l1' = List.filter (fun c1 ->
        let c1' = instantiate_evar_array evi1 c1 argsv1 in
        let filter c2 =
          let compatibility = filter_compatible_candidates conv_algo env evd evi2 argsv2 c1' c2 in
          match compatibility with
          | None -> false
          | Some _ -> true
        in
        let filtered = List.filter filter l2 in
        match filtered with [] -> false | _ -> true) l1 in
      if Int.equal (List.length l1) (List.length l1') then NoUpdate
      else UpdateWith l1'

exception CannotProject of evar_map * existential

(* Assume that FV(?n[x1:=t1..xn:=tn]) belongs to some set U.
   Can ?n be instantiated by a term u depending essentially on xi such that the
   FV(u[x1:=t1..xn:=tn]) are in the set U?
   - If ti is a variable, it has to be in U.
   - If ti is a constructor, its parameters cannot be erased even if u
     matches on it, so we have to discard ti if the parameters
     contain variables not in U.
   - If ti is rigid, we have to discard it if it contains variables in U.

  Note: when restricting as part of an equation ?n[x1:=t1..xn:=tn] = ?m[...]
  then, occurrences of ?m in the ti can be seen, like variables, as occurrences
  of subterms to eventually discard so as to be allowed to keep ti.
*)

let rec is_constrainable_in top k (ev,(fv_rels,fv_ids) as g) t =
  let f,args = decompose_app_vect t in
  match kind_of_term f with
  | Construct ((ind,_),u) ->
    let n = Inductiveops.inductive_nparams ind in
    if n > Array.length args then true (* We don't try to be more clever *)
    else
      let params = fst (Array.chop n args) in
      Array.for_all (is_constrainable_in false k g) params
  | Ind _ -> Array.for_all (is_constrainable_in false k g) args
  | Prod (_,t1,t2) -> is_constrainable_in false k g t1 && is_constrainable_in false k g t2
  | Evar (ev',_) -> top || not (Evar.equal ev' ev) (*If ev' needed, one may also try to restrict it*)
  | Var id -> Id.Set.mem id fv_ids
  | Rel n -> n <= k || Int.Set.mem n fv_rels
  | Sort _ -> true
  | _ -> (* We don't try to be more clever *) true

let has_constrainable_free_vars evd aliases k ev (fv_rels,fv_ids as fvs) t =
  let t = expansion_of_var aliases t in
  match kind_of_term t with
  | Var id -> Id.Set.mem id fv_ids
  | Rel n -> n <= k || Int.Set.mem n fv_rels
  | _ -> is_constrainable_in true k (ev,fvs) t

let ensure_evar_independent g env evd (evk1,argsv1 as ev1) (evk2,argsv2 as ev2)=
  let filter1 =
    restrict_upon_filter evd evk1 (noccur_evar env evd evk2) argsv1
  in
  let candidates1 = restrict_candidates g env evd filter1 ev1 ev2 in
  let evd,(evk1,_ as ev1) = do_restrict_hyps evd ev1 filter1 candidates1 in
  let filter2 =
    restrict_upon_filter evd evk2 (noccur_evar env evd evk1) argsv2
  in
  let candidates2 = restrict_candidates g env evd filter2 ev2 ev1 in
  let evd,ev2 = do_restrict_hyps evd ev2 filter2 candidates2 in
  evd,ev1,ev2

exception EvarSolvedOnTheFly of evar_map * constr

(* Try to project evk1[argsv1] on evk2[argsv2], if [ev1] is a pattern on
   the common domain of definition *)
let project_evar_on_evar g env evd aliases k2 pbty (evk1,argsv1 as ev1) (evk2,argsv2 as ev2) =
  (* Apply filtering on ev1 so that fvs(ev1) are in fvs(ev2). *)
  let fvs2 = free_vars_and_rels_up_alias_expansion aliases (mkEvar ev2) in
  let filter1 = restrict_upon_filter evd evk1
    (has_constrainable_free_vars evd aliases k2 evk2 fvs2)
    argsv1 in
  let candidates1 =
    try restrict_candidates g env evd filter1 ev1 ev2
    with DoesNotPreserveCandidateRestriction ->
      let evd,ev1' = do_restrict_hyps evd ev1 filter1 NoUpdate in
      raise (CannotProject (evd,ev1')) in
  let evd,(evk1',args1 as ev1') =
    try do_restrict_hyps evd ev1 filter1 candidates1
    with EvarSolvedWhileRestricting (evd,ev1) ->
      raise (EvarSolvedOnTheFly (evd,ev1)) in
  (* Only try pruning on variable substitutions, postpone otherwise. *)
  (* Rules out non-linear instances. *)
  if Option.is_empty pbty && is_unification_pattern_pure_evar env evd ev2 (mkEvar ev1) then
    try
      evd,mkEvar (evk1',invert_invertible_arg env evd aliases k2 ev2 args1)
    with NotEnoughInformationToInvert ->
      raise (CannotProject (evd,ev1'))
  else
    raise (CannotProject (evd,ev1'))

exception IllTypedInstance of env * types * types

let check_evar_instance evd evk1 body conv_algo =
  let evi = Evd.find evd evk1 in
  let evenv = evar_env evi in
  (* FIXME: The body might be ill-typed when this is called from w_merge *)
  (* This happens in practice, cf MathClasses build failure on 2013-3-15 *)
  let ty =
    try Retyping.get_type_of ~lax:true evenv evd body
    with Retyping.RetypeError _ -> error "Ill-typed evar instance"
  in
  match conv_algo evenv evd Reduction.CUMUL ty evi.evar_concl with
  | Success evd -> evd
  | UnifFailure _ -> raise (IllTypedInstance (evenv,ty,evi.evar_concl))

let solve_evar_evar_l2r f g env evd aliases pbty ev1 (evk2,_ as ev2) =
  try
    let evd,body = project_evar_on_evar g env evd aliases 0 pbty ev1 ev2 in
    let evd' = Evd.define evk2 body evd in
      check_evar_instance evd' evk2 body g
  with EvarSolvedOnTheFly (evd,c) ->
    f env evd pbty ev2 c

let opp_problem = function None -> None | Some b -> Some (not b)

let preferred_orientation evd evk1 evk2 =
  let _,src1 = (Evd.find_undefined evd evk1).evar_source in
  let _,src2 = (Evd.find_undefined evd evk2).evar_source in
  (* This is a heuristic useful for program to work *)
  match src1,src2 with
  | Evar_kinds.QuestionMark _, _ -> true
  | _,Evar_kinds.QuestionMark _ -> false
  | _ -> true

let solve_evar_evar_aux f g env evd pbty (evk1,args1 as ev1) (evk2,args2 as ev2) =
  let aliases = make_alias_map env in
  if preferred_orientation evd evk1 evk2 then
    try solve_evar_evar_l2r f g env evd aliases (opp_problem pbty) ev2 ev1
    with CannotProject (evd,ev2) ->
    try solve_evar_evar_l2r f g env evd aliases pbty ev1 ev2
    with CannotProject (evd,ev1) ->
    add_conv_oriented_pb (pbty,env,mkEvar ev1,mkEvar ev2) evd
  else
    try solve_evar_evar_l2r f g env evd aliases pbty ev1 ev2
    with CannotProject (evd,ev1) ->
    try solve_evar_evar_l2r f g env evd aliases (opp_problem pbty) ev2 ev1
    with CannotProject (evd,ev2) ->
    add_conv_oriented_pb (pbty,env,mkEvar ev1,mkEvar ev2) evd

let solve_evar_evar ?(force=false) f g env evd pbty ev1 ev2 =
  let (evd,(evk1,args1 as ev1),(evk2,args2 as ev2)),pbty =
    (* If an evar occurs in the instance of the other evar and the
       use of an heuristic is forced, we restrict *)
    if force then ensure_evar_independent g env evd ev1 ev2, None
    else (evd,ev1,ev2),pbty in
  let evi = Evd.find evd evk1 in
  let evd =
    try 
      (* ?X : Π Δ. Type i = ?Y : Π Δ'. Type j.
	 The body of ?X and ?Y just has to be of type Π Δ. Type k for some k <= i, j. *)
      let evienv = Evd.evar_env evi in
      let ctx1, i = Reduction.dest_arity evienv evi.evar_concl in
      let evi2 = Evd.find evd evk2 in
      let evi2env = Evd.evar_env evi2 in
      let ctx2, j = Reduction.dest_arity evi2env evi2.evar_concl in
      let ui, uj = univ_of_sort i, univ_of_sort j in
	if i == j || Evd.check_eq evd ui uj
	then (* Shortcut, i = j *) 
	  evd
	else if Evd.check_leq evd ui uj then
          let t2 = it_mkProd_or_LetIn (mkSort i) ctx2 in
          downcast evk2 t2 evd
	else if Evd.check_leq evd uj ui then
          let t1 = it_mkProd_or_LetIn (mkSort j) ctx1 in
          downcast evk1 t1 evd
	else
	  let evd, k = Evd.new_sort_variable univ_flexible_alg evd in
          let t1 = it_mkProd_or_LetIn (mkSort k) ctx1 in
          let t2 = it_mkProd_or_LetIn (mkSort k) ctx2 in
	  let evd = Evd.set_leq_sort env (Evd.set_leq_sort env evd k i) k j in
          downcast evk2 t2 (downcast evk1 t1 evd)
    with Reduction.NotArity -> 
      evd in
  solve_evar_evar_aux f g env evd pbty ev1 ev2

type conv_fun =
  env ->  evar_map -> conv_pb -> constr -> constr -> unification_result

type conv_fun_bool =
  env ->  evar_map -> conv_pb -> constr -> constr -> bool

(* Solve pbs ?e[t1..tn] = ?e[u1..un] which arise often in fixpoint
 * definitions. We try to unify the ti with the ui pairwise. The pairs
 * that don't unify are discarded (i.e. ?e is redefined so that it does not
 * depend on these args). *)

let solve_refl ?(can_drop=false) conv_algo env evd pbty evk argsv1 argsv2 =
  let evdref = ref evd in
  if Array.equal (e_eq_constr_univs evdref) argsv1 argsv2 then !evdref else
  (* Filter and restrict if needed *)
  let args = Array.map2 (fun a1 a2 -> (a1, a2)) argsv1 argsv2 in
  let untypedfilter =
    restrict_upon_filter evd evk
      (fun (a1,a2) -> conv_algo env evd Reduction.CONV a1 a2) args in
  let candidates = filter_candidates evd evk untypedfilter NoUpdate in
  let filter = closure_of_filter evd evk untypedfilter in
  let evd,ev1 = restrict_applied_evar evd (evk,argsv1) filter candidates in
  if Evar.equal (fst ev1) evk && can_drop then (* No refinement *) evd else
    (* either progress, or not allowed to drop, e.g. to preserve possibly *)
    (* informative equations such as ?e[x:=?y]=?e[x:=?y'] where we don't know *)
    (* if e can depend on x until ?y is not resolved, or, conversely, we *)
    (* don't know if ?y has to be unified with ?y, until e is resolved *)
  let argsv2 = restrict_instance evd evk filter argsv2 in
  let ev2 = (fst ev1,argsv2) in
  (* Leave a unification problem *)
  add_conv_oriented_pb (pbty,env,mkEvar ev1,mkEvar ev2) evd

(* If the evar can be instantiated by a finite set of candidates known
   in advance, we check which of them apply *)

exception NoCandidates
exception IncompatibleCandidates

let solve_candidates conv_algo env evd (evk,argsv) rhs =
  let evi = Evd.find evd evk in
  match evi.evar_candidates with
  | None -> raise NoCandidates
  | Some l ->
      let l' =
        List.map_filter
          (filter_compatible_candidates conv_algo env evd evi argsv rhs) l in
      match l' with
      | [] -> raise IncompatibleCandidates
      | [c,evd] ->
          (* solve_candidates might have been called recursively in the mean *)
          (* time and the evar been solved by the filtering process *)
          if Evd.is_undefined evd evk then Evd.define evk c evd else evd
      | l when List.length l < List.length l' ->
          let candidates = List.map fst l in
          restrict_evar evd evk None (UpdateWith candidates)
      | l -> evd

(* We try to instantiate the evar assuming the body won't depend
 * on arguments that are not Rels or Vars, or appearing several times
 * (i.e. we tackle a generalization of Miller-Pfenning patterns unification)
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
 * have succeeded after some reductions.
 *
 * This is the work of [invert_definition Γ Σ ?ev[hyps:=args] c]
 * Precondition:  Σ; Γ, y1..yk |- c /\ Σ; Γ |- u1..un
 * Postcondition: if φ(x1..xn) is returned then
 *                Σ; Γ, y1..yk |- φ(u1..un) = c /\ x1..xn |- φ(x1..xn)
 *)

exception NotInvertibleUsingOurAlgorithm of constr
exception NotEnoughInformationToProgress of (Id.t * evar_projection) list
exception NotEnoughInformationEvarEvar of constr
exception OccurCheckIn of evar_map * constr
exception MetaOccurInBodyInternal

let rec invert_definition conv_algo choose env evd pbty (evk,argsv as ev) rhs =
  let aliases = make_alias_map env in
  let evdref = ref evd in
  let progress = ref false in
  let evi = Evd.find evd evk in
  let subst,cstr_subst = make_projectable_subst aliases evd evi argsv in

  (* Projection *)
  let project_variable t =
    (* Evar/Var problem: unifiable iff variable projectable from ev subst *)
    try
      let sols = find_projectable_vars true aliases !evdref t subst in
      let c, p = match sols with
        | [] -> raise Not_found
        | [id,p] -> (mkVar id, p)
        | (id,p)::_::_ ->
            if choose then (mkVar id, p) else raise (NotUniqueInType sols)
      in
      let ty = lazy (Retyping.get_type_of env !evdref t) in
      let evd = do_projection_effects (evar_define conv_algo ~choose) env ty !evdref p in
      evdref := evd;
      c
    with
      | Not_found -> raise (NotInvertibleUsingOurAlgorithm t)
      | NotUniqueInType sols ->
          if not !progress then
            raise (NotEnoughInformationToProgress sols);
          (* No unique projection but still restrict to where it is possible *)
          (* materializing is necessary, but is restricting useful? *)
          let ty = find_solution_type (evar_filtered_env evi) sols in
          let ty' = instantiate_evar_array evi ty argsv in
          let (evd,evar,(evk',argsv' as ev')) =
            materialize_evar (evar_define conv_algo ~choose) env !evdref 0 ev ty' in
          let ts = expansions_of_var aliases t in
          let test c = isEvar c || List.mem_f Constr.equal c ts in
          let filter = restrict_upon_filter evd evk test argsv' in
          let filter = closure_of_filter evd evk' filter in
          let candidates = extract_candidates sols in
          let evd = match candidates with
          | NoUpdate ->
            let evd, ev'' = restrict_applied_evar evd ev' filter NoUpdate in
            Evd.add_conv_pb (Reduction.CONV,env,mkEvar ev'',t) evd
          | UpdateWith _ ->
            restrict_evar evd evk' filter candidates
          in
          evdref := evd;
          evar in

  let rec imitate (env',k as envk) t =
    let t = whd_evar !evdref t in
    match kind_of_term t with
    | Rel i when i>k ->
        (match pi2 (Environ.lookup_rel (i-k) env') with
        | None -> project_variable (mkRel (i-k))
        | Some b ->
          try project_variable (mkRel (i-k))
          with NotInvertibleUsingOurAlgorithm _ -> imitate envk (lift i b))
    | Var id ->
        (match pi2 (Environ.lookup_named id env') with
        | None -> project_variable t
        | Some b ->
          try project_variable t
          with NotInvertibleUsingOurAlgorithm _ -> imitate envk b)
    | LetIn (na,b,u,c) ->
        imitate envk (subst1 b c)
    | Evar (evk',args' as ev') ->
        if Evar.equal evk evk' then raise (OccurCheckIn (evd,rhs));
        (* Evar/Evar problem (but left evar is virtual) *)
        let aliases = lift_aliases k aliases in
        (try
          let ev = (evk,Array.map (lift k) argsv) in
          let evd,body = project_evar_on_evar conv_algo env' !evdref aliases k None ev' ev in
          evdref := evd;
          body
        with
        | EvarSolvedOnTheFly (evd,t) -> evdref:=evd; imitate envk t
        | CannotProject (evd,ev') ->
          if not !progress then
            raise (NotEnoughInformationEvarEvar t);
          (* Make the virtual left evar real *)
          let ty = get_type_of env' evd t in
          let (evd,evar'',ev'') =
             materialize_evar (evar_define conv_algo ~choose) env' evd k ev ty in
          (* materialize_evar may instantiate ev' by another evar; adjust it *)
          let (evk',args' as ev') = normalize_evar evd ev' in
          let evd =
             (* Try to project (a restriction of) the left evar ... *)
            try
              let evd,body = project_evar_on_evar conv_algo env' evd aliases 0 None ev'' ev' in
              let evd = Evd.define evk' body evd in
		check_evar_instance evd evk' body conv_algo
            with
            | EvarSolvedOnTheFly _ -> assert false (* ev has no candidates *)
            | CannotProject (evd,ev'') ->
              (* ... or postpone the problem *)
              add_conv_oriented_pb (None,env',mkEvar ev'',mkEvar ev') evd in
          evdref := evd;
          evar'')
    | _ ->
        progress := true;
        match
          let c,args = decompose_app_vect t in
          match kind_of_term c with
          | Construct (cstr,u) when noccur_between 1 k t ->
            (* This is common case when inferring the return clause of match *)
            (* (currently rudimentary: we do not treat the case of multiple *)
            (*  possible inversions; we do not treat overlap with a possible *)
            (*  alternative inversion of the subterms of the constructor, etc)*)
            (match find_projectable_constructor env evd cstr k args cstr_subst with
             | _::_ as l -> Some (List.map mkVar l)
             | _ -> None)
          | _ -> None
        with
        | Some l ->
            let ty = get_type_of env' !evdref t in
            let candidates =
              try
                let t =
                  map_constr_with_full_binders (fun d (env,k) -> push_rel d env, k+1)
                    imitate envk t in
                t::l
              with e when Errors.noncritical e -> l in
            (match candidates with
            | [x] -> x
            | _ ->
              let (evd,evar'',ev'') =
                materialize_evar (evar_define conv_algo ~choose) env' !evdref k ev ty in
              evdref := restrict_evar evd (fst ev'') None (UpdateWith candidates);
              evar'')
        | None ->
          (* Evar/Rigid problem (or assimilated if not normal): we "imitate" *)
            map_constr_with_full_binders (fun d (env,k) -> push_rel d env, k+1)
              imitate envk t in

  let _fast rhs = 
    let filter_ctxt = evar_filtered_context evi in
    let names = ref Idset.empty in
    let rec is_id_subst ctxt s =
       match ctxt, s with
         | ((id, _, _) :: ctxt'), (c :: s') ->
           names := Idset.add id !names;
           isVarId id c && is_id_subst ctxt' s'
         | [], [] -> true
         | _ -> false in
    is_id_subst filter_ctxt (Array.to_list argsv) &&
    closed0 rhs &&
    Idset.subset (collect_vars rhs) !names in
  let rhs = whd_beta evd rhs (* heuristic *) in
  let fast rhs = 
    let filter_ctxt = evar_filtered_context evi in
    let names = ref Idset.empty in
    let rec is_id_subst ctxt s =
      match ctxt, s with
      | ((id, _, _) :: ctxt'), (c :: s') ->
        names := Idset.add id !names;
        isVarId id c && is_id_subst ctxt' s'
      | [], [] -> true
      | _ -> false 
    in
      is_id_subst filter_ctxt (Array.to_list argsv) &&
      closed0 rhs &&
      Idset.subset (collect_vars rhs) !names 
  in
  let body =
    if fast rhs then nf_evar evd rhs
    else imitate (env,0) rhs
 in (!evdref,body)

(* [define] tries to solve the problem "?ev[args] = rhs" when "?ev" is
 * an (uninstantiated) evar such that "hyps |- ?ev : typ". Otherwise said,
 * [define] tries to find an instance lhs such that
 * "lhs [hyps:=args]" unifies to rhs. The term "lhs" must be closed in
 * context "hyps" and not referring to itself.
 *)

and evar_define conv_algo ?(choose=false) env evd pbty (evk,argsv as ev) rhs =
  match kind_of_term rhs with
  | Evar (evk2,argsv2 as ev2) ->
      if Evar.equal evk evk2 then
        solve_refl ~can_drop:choose
          (test_success conv_algo) env evd pbty evk argsv argsv2
      else
        solve_evar_evar ~force:choose
          (evar_define conv_algo) conv_algo env evd pbty ev ev2
  | _ ->
  try solve_candidates conv_algo env evd ev rhs
  with NoCandidates ->
  try
    let (evd',body) = invert_definition conv_algo choose env evd pbty ev rhs in
    if occur_meta body then raise MetaOccurInBodyInternal;
    (* invert_definition may have instantiate some evars of rhs with evk *)
    (* so we recheck acyclicity *)
    if occur_evar evk body then raise (OccurCheckIn (evd',body));
    (* needed only if an inferred type *)
    let evd', body = refresh_universes pbty env evd' body in
(* Cannot strictly type instantiations since the unification algorithm
 * does not unify applications from left to right.
 * e.g problem f x == g y yields x==y and f==g (in that order)
 * Another problem is that type variables are evars of type Type
   let _ =
      try
        let env = evar_filtered_env evi in
        let ty = evi.evar_concl in
        Typing.check env evd' body ty
      with e ->
        msg_info
          (str "Ill-typed evar instantiation: " ++ fnl() ++
           pr_evar_map evd' ++ fnl() ++
           str "----> " ++ int ev ++ str " := " ++
           print_constr body);
        raise e in*)
    let evd' = check_evar_instance evd' evk body conv_algo in
    Evd.define evk body evd'
  with
    | NotEnoughInformationToProgress sols ->
        postpone_non_unique_projection env evd pbty ev sols rhs
    | NotEnoughInformationEvarEvar t ->
        add_conv_oriented_pb (pbty,env,mkEvar ev,t) evd
    | NotInvertibleUsingOurAlgorithm _ | MetaOccurInBodyInternal as e ->
        raise e
    | OccurCheckIn (evd,rhs) ->
        (* last chance: rhs actually reduces to ev *)
        let c = whd_betadeltaiota env evd rhs in
        match kind_of_term c with
        | Evar (evk',argsv2) when Evar.equal evk evk' ->
	    solve_refl (fun env sigma pb c c' -> is_fconv pb env sigma c c')
              env evd pbty evk argsv argsv2
        | _ ->
	    raise (OccurCheckIn (evd,rhs))

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
 * define
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
  (try Evar.Set.mem (head_evar t1) lev with NoHeadEvar -> false) ||
  (try Evar.Set.mem (head_evar t2) lev with NoHeadEvar -> false)

let reconsider_conv_pbs conv_algo evd =
  let (evd,pbs) = extract_changed_conv_pbs evd status_changed in
  List.fold_left
    (fun p (pbty,env,t1,t2 as x) ->
       match p with
       | Success evd ->
           (match conv_algo env evd pbty t1 t2 with
           | Success _ as x -> x
           | UnifFailure (i,e) -> UnifFailure (i,CannotSolveConstraint (x,e)))
       | UnifFailure _ as x -> x)
    (Success evd)
    pbs

(* Tries to solve problem t1 = t2.
 * Precondition: t1 is an uninstantiated evar
 * Returns an optional list of evars that were instantiated, or None
 * if the problem couldn't be solved. *)

(* Rq: uncomplete algorithm if pbty = CONV_X_LEQ ! *)
let solve_simple_eqn conv_algo ?(choose=false) env evd (pbty,(evk1,args1 as ev1),t2) =
  try
    let t2 = whd_betaiota evd t2 in (* includes whd_evar *)
    let evd = evar_define conv_algo ~choose env evd pbty ev1 t2 in
      reconsider_conv_pbs conv_algo evd
  with
    | NotInvertibleUsingOurAlgorithm t ->
        UnifFailure (evd,NotClean (ev1,env,t))
    | OccurCheckIn (evd,rhs) ->
        UnifFailure (evd,OccurCheck (evk1,rhs))
    | MetaOccurInBodyInternal ->
        UnifFailure (evd,MetaOccurInBody evk1)
    | IllTypedInstance (env,t,u) ->
        UnifFailure (evd,InstanceNotSameType (evk1,env,t,u))
    | IncompatibleCandidates ->
        UnifFailure (evd,ConversionFailed (env,mkEvar ev1,t2))

