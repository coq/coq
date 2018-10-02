(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Pp
open Util
open Names
open Constr
open Termops
open Environ
open EConstr
open Vars
open Namegen
open Evd
open Reduction
open Reductionops
open Evarutil
open Evardefine
open Evarsolve
open Pretype_errors
open Retyping
open Coercion
open Recordops
open Locus
open Locusops
open Find_subterm

type metabinding = (metavariable * EConstr.constr * (instance_constraint * instance_typing_status))

type subst0 =
  (evar_map *
    metabinding list *
      (Environ.env * EConstr.existential * EConstr.t) list)

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let keyed_unification = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Unification is keyed";
  Goptions.optkey = ["Keyed";"Unification"];
  Goptions.optread = (fun () -> !keyed_unification);
  Goptions.optwrite = (fun a -> keyed_unification:=a);
}

let is_keyed_unification () = !keyed_unification

let debug_unification = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname =
    "Print states sent to tactic unification";
  Goptions.optkey = ["Debug";"Tactic";"Unification"];
  Goptions.optread = (fun () -> !debug_unification);
  Goptions.optwrite = (fun a -> debug_unification:=a);
}

(** Making this unification algorithm correct w.r.t. the evar-map abstraction
    breaks too much stuff. So we redefine incorrect functions here. *)

let unsafe_occur_meta_or_existential c =
  let c = EConstr.Unsafe.to_constr c in
  let rec occrec c = match Constr.kind c with
    | Evar _ -> raise Occur
    | Meta _ -> raise Occur
    | _ -> Constr.iter occrec c
  in try occrec c; false with Occur -> true


let occur_meta_or_undefined_evar evd c =
  (** This is performance-critical. Using the evar-insensitive API changes the
      resulting heuristic. *)
  let c = EConstr.Unsafe.to_constr c in
  let rec occrec c = match Constr.kind c with
    | Meta _ -> raise Occur
    | Evar (ev,args) ->
        (match evar_body (Evd.find evd ev) with
        | Evar_defined c ->
            occrec (EConstr.Unsafe.to_constr c); Array.iter occrec args
        | Evar_empty -> raise Occur)
    | _ -> Constr.iter occrec c
  in try occrec c; false with Occur | Not_found -> true

let occur_meta_evd sigma mv c =
  let rec occrec c =
    (* Note: evars are not instantiated by terms with metas *)
    let c = whd_meta sigma c in
    match EConstr.kind sigma c with
    | Meta mv' when Int.equal mv mv' -> raise Occur
    | _ -> EConstr.iter sigma occrec c
  in try occrec c; false with Occur -> true

(* if lname_typ is [xn,An;..;x1,A1] and l is a list of terms,
   gives [x1:A1]..[xn:An]c' such that c converts to ([x1:A1]..[xn:An]c' l) *)

let abstract_scheme env evd c l lname_typ =
  let mkLambda_name env (n,a,b) =
    mkLambda (named_hd env evd a n, a, b)
  in
  List.fold_left2
    (fun (t,evd) (locc,a) decl ->
       let na = RelDecl.get_name decl in
       let ta = RelDecl.get_type decl in
       let na = match EConstr.kind evd a with Var id -> Name id | _ -> na in
(* [occur_meta ta] test removed for support of eelim/ecase but consequences
   are unclear...
       if occur_meta ta then error "cannot find a type for the generalisation"
       else *) 
       if occur_meta evd a then mkLambda_name env (na,ta,t), evd
       else
	 let t', evd' = Find_subterm.subst_closed_term_occ env evd locc a t in
	   mkLambda_name env (na,ta,t'), evd')
    (c,evd)
    (List.rev l)
    lname_typ

(* Precondition: resulting abstraction is expected to be of type [typ] *)

let abstract_list_all env evd typ c l =
  let ctxt,_ = splay_prod_n env evd (List.length l) typ in
  let l_with_all_occs = List.map (function a -> (LikeFirst,a)) l in
  let p,evd = abstract_scheme env evd c l_with_all_occs ctxt in
  let evd,typp =
    try Typing.type_of env evd p
    with
    | UserError _ ->
        error_cannot_find_well_typed_abstraction env evd p l None
    | Type_errors.TypeError (env',x) ->
        (** FIXME: plug back the typing information *)
        error_cannot_find_well_typed_abstraction env evd p l None
    | Pretype_errors.PretypeError (env',evd,TypingError x) ->
        error_cannot_find_well_typed_abstraction env evd p l (Some (env',x)) in
  evd,(p,typp)

let set_occurrences_of_last_arg args =
  Some AllOccurrences :: List.tl (Array.map_to_list (fun _ -> None) args)

let abstract_list_all_with_dependencies env evd typ c l =
  let (evd, ev) = new_evar env evd typ in
  let evd,ev' = evar_absorb_arguments env evd (destEvar evd ev) l in
  let n = List.length l in
  let argoccs = set_occurrences_of_last_arg (Array.sub (snd ev') 0 n) in
  let evd,b =
    Evarconv.second_order_matching empty_transparent_state
      env evd ev' argoccs c in
  if b then
    let p = nf_evar evd ev in
      evd, p
  else error_cannot_find_well_typed_abstraction env evd 
    c l None

(**)

(* A refinement of [conv_pb]: the integers tells how many arguments
   were applied in the context of the conversion problem; if the number
   is non zero, steps of eta-expansion will be allowed
*)

let opp_status = function
  | IsSuperType -> IsSubType
  | IsSubType -> IsSuperType
  | Conv -> Conv

let add_type_status (x,y) = ((x,TypeNotProcessed),(y,TypeNotProcessed))

let extract_instance_status = function
  | CUMUL -> add_type_status (IsSubType, IsSuperType)
  | CONV -> add_type_status (Conv, Conv)

let rec subst_meta_instances sigma bl c =
  match EConstr.kind sigma c with
    | Meta i ->
      let select (j,_,_) = Int.equal i j in
      (try pi2 (List.find select bl) with Not_found -> c)
    | _ -> EConstr.map sigma (subst_meta_instances sigma bl) c

(** [env] should be the context in which the metas live *)

let pose_all_metas_as_evars env evd t =
  let evdref = ref evd in
  let rec aux t = match EConstr.kind !evdref t with
  | Meta mv ->
      (match Evd.meta_opt_fvalue !evdref mv with
       | Some ({rebus=c},_) -> c
       | None ->
        let {rebus=ty;freemetas=mvs} = Evd.meta_ftype evd mv in
        let ty = if Evd.Metaset.is_empty mvs then ty else aux ty in
        let ty = nf_betaiota env evd ty in
        let src = Evd.evar_source_of_meta mv !evdref in
        let evd, ev = Evarutil.new_evar env !evdref ~src ty in
        evdref := meta_assign mv (ev,(Conv,TypeNotProcessed)) evd;
        ev)
  | _ ->
      EConstr.map !evdref aux t in
  let c = aux t in
  (* side-effect *)
  (!evdref, c)

let solve_pattern_eqn_array (env,nb) f l c (sigma,metasubst,evarsubst : subst0) =
  match EConstr.kind sigma f with
    | Meta k ->
	(* We enforce that the Meta does not depend on the [nb]
	   extra assumptions added by unification to the context *)
        let env' = pop_rel_context nb env in
	let sigma,c = pose_all_metas_as_evars env' sigma c in
	let c = solve_pattern_eqn env sigma l c in
	let pb = (Conv,TypeNotProcessed) in
	  if noccur_between sigma 1 nb c then
            sigma,(k,lift (-nb) c,pb)::metasubst,evarsubst
	  else
            let l = List.map of_alias l in
            error_cannot_unify_local env sigma (applist (f, l),c,c)
    | Evar ev ->
        let env' = pop_rel_context nb env in
	let sigma,c = pose_all_metas_as_evars env' sigma c in
	sigma,metasubst,(env,ev,solve_pattern_eqn env sigma l c)::evarsubst
    | _ -> assert false

let push d (env,n) = (push_rel_assum d env,n+1)

(*******************************)

(* Unification à l'ordre 0 de m et n: [unify_0 env sigma cv_pb m n]
   renvoie deux listes:

   metasubst:(int*constr)list    récolte les instances des (Meta k)
   evarsubst:(constr*constr)list récolte les instances des (Const "?k")

   Attention : pas d'unification entre les différences instances d'une
   même meta ou evar, il peut rester des doublons *)

(* Unification order: *)
(* Left to right: unifies first argument and then the other arguments *)
(*let unify_l2r x = List.rev x
(* Right to left: unifies last argument and then the other arguments *)
let unify_r2l x = x

let sort_eqns = unify_r2l
*)

type core_unify_flags = {
  modulo_conv_on_closed_terms : Names.transparent_state option;
    (* What this flag controls was activated with all constants transparent, *)
    (* even for auto, since Coq V5.10 *)

  use_metas_eagerly_in_conv_on_closed_terms : bool;
    (* This refinement of the conversion on closed terms is activable *)
    (* (and activated for apply, rewrite but not auto since Feb 2008 for 8.2) *)

  use_evars_eagerly_in_conv_on_closed_terms : bool;

  modulo_delta : Names.transparent_state;
    (* This controls which constants are unfoldable; this is on for apply *)
    (* (but not simple apply) since Feb 2008 for 8.2 *)

  modulo_delta_types : Names.transparent_state;

  check_applied_meta_types : bool;
    (* This controls whether meta's applied to arguments have their *)
    (* type unified with the type of their instance *)

  use_pattern_unification : bool;
    (* This solves pattern "?n x1 ... xn = t" when the xi are distinct rels *)
    (* This says if pattern unification is tried *)

  use_meta_bound_pattern_unification : bool;
    (* This is implied by use_pattern_unification; has no particular *)
    (* reasons to be set differently than use_pattern_unification *)
    (* except for compatibility of "auto". *)
    (* This was on for all tactics, including auto, since Sep 2006 for 8.1 *)
    (* This allowed for instance to unify "forall x:?A, ?B x" with "A' -> B'" *)
    (* when ?B is a Meta. *)

  frozen_evars : Evar.Set.t;
    (* Evars of this set are considered axioms and never instantiated *)
    (* Useful e.g. for autorewrite *)

  restrict_conv_on_strict_subterms : bool;
    (* No conversion at the root of the term; potentially useful for rewrite *)

  modulo_betaiota : bool;
    (* Support betaiota in the reduction *)
    (* Note that zeta is always used *)

  modulo_eta : bool;
    (* Support eta in the reduction *)
}

type unify_flags = {
  core_unify_flags : core_unify_flags;
    (* Governs unification of problems of the form "t(?x) = u(?x)" in apply *)

  merge_unify_flags : core_unify_flags;
    (* These are the flags to be used when trying to unify *)
    (* several instances of the same metavariable *)
    (* Typical situation is when we give a pattern to be matched *)
    (* syntactically against a subterm but we want the metas of the *)
    (* pattern to be modulo convertibility *)

  subterm_unify_flags : core_unify_flags;
    (* Governs unification of problems of the form "?X a1..an = u" in apply, *)
    (* hence in rewrite and elim *)

  allow_K_in_toplevel_higher_order_unification : bool;
    (* Tells in second-order abstraction over subterms which have not *)
    (* been found in term are allowed (used for rewrite, elim, or *)
    (* apply with a lemma whose type has the form "?X a1 ... an") *)

  resolve_evars : bool
    (* This says if type classes instances resolution must be used to infer *)
    (* the remaining evars *)
}

(* Default flag for unifying a type against a type (e.g. apply) *)
(* We set all conversion flags (no flag should be modified anymore) *)
let default_core_unify_flags () =
  let ts = Names.full_transparent_state in {
  modulo_conv_on_closed_terms = Some ts;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = ts;
  modulo_delta_types = ts;
  check_applied_meta_types = true;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  frozen_evars = Evar.Set.empty;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = true;
  modulo_eta = true;
 }

(* Default flag for first-order or second-order unification of a type *)
(* against another type (e.g. apply)                                  *)
(* We set all conversion flags (no flag should be modified anymore)   *)
let default_unify_flags () =
  let flags = default_core_unify_flags () in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = var_full_transparent_state };
  allow_K_in_toplevel_higher_order_unification = false; (* Why not? *)
  resolve_evars = false
}

let set_no_delta_core_flags flags = { flags with
  modulo_conv_on_closed_terms = None;
  modulo_delta = empty_transparent_state;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  modulo_betaiota = false
}

let set_no_delta_flags flags = {
  core_unify_flags = set_no_delta_core_flags flags.core_unify_flags;
  merge_unify_flags = set_no_delta_core_flags flags.merge_unify_flags;
  subterm_unify_flags = set_no_delta_core_flags flags.subterm_unify_flags;
  allow_K_in_toplevel_higher_order_unification =
      flags.allow_K_in_toplevel_higher_order_unification;
  resolve_evars = flags.resolve_evars
}

(* For the first phase of keyed unification, restrict
  to conversion (including beta-iota) only on closed terms *)
let set_no_delta_open_core_flags flags = { flags with
  modulo_delta = empty_transparent_state;
  modulo_betaiota = false;
}

let set_no_delta_open_flags flags = {
  core_unify_flags = set_no_delta_open_core_flags flags.core_unify_flags;
  merge_unify_flags = set_no_delta_open_core_flags flags.merge_unify_flags;
  subterm_unify_flags = set_no_delta_open_core_flags flags.subterm_unify_flags;
  allow_K_in_toplevel_higher_order_unification =
      flags.allow_K_in_toplevel_higher_order_unification;
  resolve_evars = flags.resolve_evars
}

(* Default flag for the "simple apply" version of unification of a *)
(* type against a type (e.g. apply) *)
(* We set only the flags available at the time the new "apply" extended *)
(* out of "simple apply" *)
let default_no_delta_core_unify_flags () = { (default_core_unify_flags ()) with
  modulo_delta = empty_transparent_state;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  modulo_betaiota = false;
}

let default_no_delta_unify_flags ts =
  let flags = default_no_delta_core_unify_flags () in
  let flags = { flags with
                modulo_conv_on_closed_terms = Some ts;
                modulo_delta_types = ts
              } in
  {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

(* Default flags for looking for subterms in elimination tactics *)
(* Not used in practice at the current date, to the exception of *)
(* allow_K) because only closed terms are involved in *)
(* induction/destruct/case/elim and w_unify_to_subterm_list does not *)
(* call w_unify for induction/destruct/case/elim  (13/6/2011) *)
let elim_core_flags sigma = { (default_core_unify_flags ()) with
  modulo_betaiota = false;
  frozen_evars =
    fold_undefined (fun evk _ evars -> Evar.Set.add evk evars)
      sigma Evar.Set.empty;
}

let elim_flags_evars sigma =
  let flags = elim_core_flags sigma in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = empty_transparent_state };
  allow_K_in_toplevel_higher_order_unification = true;
  resolve_evars = false
}

let elim_flags () = elim_flags_evars Evd.empty

let elim_no_delta_core_flags () = { (elim_core_flags Evd.empty) with
  modulo_delta = empty_transparent_state;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  modulo_betaiota = false;
}

let elim_no_delta_flags () =
  let flags = elim_no_delta_core_flags () in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = flags;
  allow_K_in_toplevel_higher_order_unification = true;
  resolve_evars = false
}

(* On types, we don't restrict unification, but possibly for delta *)
let set_flags_for_type flags = { flags with
  modulo_delta = flags.modulo_delta_types;
  modulo_conv_on_closed_terms = Some flags.modulo_delta_types;
  use_pattern_unification = true;
  modulo_betaiota = true;
  modulo_eta = true;
}

let use_evars_pattern_unification flags =
  flags.use_pattern_unification

let use_metas_pattern_unification sigma flags nb l =
  flags.use_pattern_unification
  || flags.use_meta_bound_pattern_unification &&
     Array.for_all (fun c -> isRel sigma c && destRel sigma c <= nb) l

type key = 
  | IsKey of CClosure.table_key
  | IsProj of Projection.t * EConstr.constr

let expand_table_key env = function
  | ConstKey cst -> constant_opt_value_in env cst
  | VarKey id -> (try named_body id env with Not_found -> None)
  | RelKey _ -> None

let unfold_projection env p stk =
  let s = Stack.Proj (p, Cst_stack.empty) in
  s :: stk

let expand_key ts env sigma = function
  | Some (IsKey k) -> Option.map EConstr.of_constr (expand_table_key env k)
  | Some (IsProj (p, c)) -> 
    let red = Stack.zip sigma (fst (whd_betaiota_deltazeta_for_iota_state ts env sigma
                               Cst_stack.empty (c, unfold_projection env p [])))
    in if EConstr.eq_constr sigma (EConstr.mkProj (p, c)) red then None else Some red
  | None -> None

let isApp_or_Proj sigma c =
  match kind sigma c with
  | App _ | Proj _ -> true
  | _ -> false
  
type unirec_flags = {
  at_top: bool;
  with_types: bool;
  with_cs : bool;
}

let subterm_restriction opt flags =
  not opt.at_top && flags.restrict_conv_on_strict_subterms

let key_of env sigma b flags f =
  if subterm_restriction b flags then None else
  match EConstr.kind sigma f with
  | Const (cst, u) when is_transparent env (ConstKey cst) &&
      (Cpred.mem cst (snd flags.modulo_delta)
       || Recordops.is_primitive_projection cst) ->
      let u = EInstance.kind sigma u in
      Some (IsKey (ConstKey (cst, u)))
  | Var id when is_transparent env (VarKey id) && 
      Id.Pred.mem id (fst flags.modulo_delta) ->
    Some (IsKey (VarKey id))
  | Proj (p, c) when Projection.unfolded p
    || (is_transparent env (ConstKey (Projection.constant p)) &&
       (Cpred.mem (Projection.constant p) (snd flags.modulo_delta))) ->
    Some (IsProj (p, c))
  | _ -> None
  

let translate_key = function
  | ConstKey (cst,u) -> ConstKey cst
  | VarKey id -> VarKey id
  | RelKey n -> RelKey n

let translate_key = function
  | IsKey k -> translate_key k    
  | IsProj (c, _) -> ConstKey (Projection.constant c)
  
let oracle_order env cf1 cf2 =
  match cf1 with
  | None ->
      (match cf2 with
      | None -> None
      | Some k2 -> Some false)
  | Some k1 ->
      match cf2 with
      | None -> Some true
      | Some k2 ->
	match k1, k2 with
	| IsProj (p, _), IsKey (ConstKey (p',_)) 
	  when Constant.equal (Projection.constant p) p' -> 
	  Some (not (Projection.unfolded p))
	| IsKey (ConstKey (p,_)), IsProj (p', _) 
	  when Constant.equal p (Projection.constant p') -> 
	  Some (Projection.unfolded p')
	| _ ->
          Some (Conv_oracle.oracle_order (fun x -> x)
		  (Environ.oracle env) false (translate_key k1) (translate_key k2))

let is_rigid_head sigma flags t =
  match EConstr.kind sigma t with
  | Const (cst,u) -> not (Cpred.mem cst (snd flags.modulo_delta))
  | Ind (i,u) -> true
  | Construct _ -> true
  | Fix _ | CoFix _ -> true
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Cast (_, _, _) | Prod (_, _, _)
    | Lambda (_, _, _) | LetIn (_, _, _, _) | App (_, _) | Case (_, _, _, _)
    | Proj (_, _) -> false (* Why aren't Prod, Sort rigid heads ? *)

let force_eqs c =
  let open UnivProblem in
  Set.fold
    (fun c acc ->
       let c' = match c with
         (* Should we be forcing weak constraints? *)
         | ULub (l, r) | UWeak (l, r) -> UEq (Univ.Universe.make l,Univ.Universe.make r)
         | ULe _ | UEq _ -> c
       in
        Set.add c' acc)
    c Set.empty

let constr_cmp pb env sigma flags t u =
  let cstrs =
    if pb == Reduction.CONV then EConstr.eq_constr_universes env sigma t u
    else EConstr.leq_constr_universes env sigma t u
  in 
  match cstrs with
  | Some cstrs ->
      begin try Some (Evd.add_universe_constraints sigma cstrs)
      with Univ.UniverseInconsistency _ -> None
      | Evd.UniversesDiffer -> 
	if is_rigid_head sigma flags t then 
          try Some (Evd.add_universe_constraints sigma (force_eqs cstrs))
          with Univ.UniverseInconsistency _ -> None
        else None
      end
  | None ->
    None
    
let do_reduce ts (env, nb) sigma c =
  Stack.zip sigma (fst (whd_betaiota_deltazeta_for_iota_state
		  ts env sigma Cst_stack.empty (c, Stack.empty)))

let isAllowedEvar sigma flags c = match EConstr.kind sigma c with
  | Evar (evk,_) -> not (Evar.Set.mem evk flags.frozen_evars)
  | _ -> false


let subst_defined_metas_evars sigma (bl,el) c =
  (** This seems to be performance-critical, and using the evar-insensitive
      primitives blow up the time passed in this function. *)
  let c = EConstr.Unsafe.to_constr c in
  let rec substrec c = match Constr.kind c with
    | Meta i ->
      let select (j,_,_) = Int.equal i j in
      substrec (EConstr.Unsafe.to_constr (pi2 (List.find select bl)))
    | Evar (evk,args) ->
      let eq c1 c2 = Constr.equal c1 (EConstr.Unsafe.to_constr c2) in
      let select (_,(evk',args'),_) = Evar.equal evk evk' && Array.for_all2 eq args args' in
      (try substrec (EConstr.Unsafe.to_constr (pi3 (List.find select el)))
       with Not_found -> Constr.map substrec c)
    | _ -> Constr.map substrec c
  in try Some (EConstr.of_constr (substrec c)) with Not_found -> None

let check_compatibility env pbty flags (sigma,metasubst,evarsubst : subst0) tyM tyN =
  match subst_defined_metas_evars sigma (metasubst,[]) tyM with
  | None -> sigma
  | Some m ->
  match subst_defined_metas_evars sigma (metasubst,[]) tyN with
  | None -> sigma
  | Some n ->
    if is_ground_term sigma m && is_ground_term sigma n then
      match infer_conv ~pb:pbty ~ts:flags.modulo_delta_types env sigma m n with
      | Some sigma -> sigma
      | None -> error_cannot_unify env sigma (m,n)
    else sigma


let rec is_neutral env sigma ts t =
  let (f, l) = decompose_app_vect sigma t in
    match EConstr.kind sigma f with
    | Const (c, u) ->
      not (Environ.evaluable_constant c env) ||
      not (is_transparent env (ConstKey c)) ||
      not (Cpred.mem c (snd ts))
    | Var id -> 
      not (Environ.evaluable_named id env) ||
      not (is_transparent env (VarKey id)) ||
      not (Id.Pred.mem id (fst ts))
    | Rel n -> true
    | Evar _ | Meta _ -> true
    | Case (_, p, c, cl) -> is_neutral env sigma ts c
    | Proj (p, c) -> is_neutral env sigma ts c
    | Lambda _ | LetIn _ | Construct _ | CoFix _ -> false
    | Sort _ | Cast (_, _, _) | Prod (_, _, _) | Ind _ -> false (* Really? *)
    | Fix _ -> false (* This is an approximation *)
    | App _ -> assert false

let is_eta_constructor_app env sigma ts f l1 term =
  match EConstr.kind sigma f with
  | Construct (((_, i as ind), j), u) when j == 1 ->
    let open Declarations in
    let mib = lookup_mind (fst ind) env in
      (match mib.Declarations.mind_record with
      | PrimRecord info when mib.Declarations.mind_finite == Declarations.BiFinite &&
          let (_, projs, _) = info.(i) in
          Array.length projs == Array.length l1 - mib.Declarations.mind_nparams ->
	(** Check that the other term is neutral *)
	is_neutral env sigma ts term
      | _ -> false)
  | _ -> false

let eta_constructor_app env sigma f l1 term =
  match EConstr.kind sigma f with
  | Construct (((_, i as ind), j), u) ->
    let mib = lookup_mind (fst ind) env in
      (match get_projections env ind with
      | Some projs ->
        let npars = mib.Declarations.mind_nparams in
	let pars, l1' = Array.chop npars l1 in
	let arg = Array.append pars [|term|] in
        let l2 = Array.map (fun p -> mkApp (mkConstU (Projection.Repr.constant p,u), arg)) projs in
	  l1', l2
      | _ -> assert false)
  | _ -> assert false

let rec unify_0_with_initial_metas (sigma,ms,es as subst : subst0) conv_at_top env cv_pb flags m n =
  let rec unirec_rec (curenv,nb as curenvnb) pb opt ((sigma,metasubst,evarsubst) as substn : subst0) curm curn =
    let cM = Evarutil.whd_head_evar sigma curm
    and cN = Evarutil.whd_head_evar sigma curn in
    let () = 
      if !debug_unification then
        Feedback.msg_debug (
          Termops.Internal.print_constr_env curenv sigma cM ++ str" ~= " ++
          Termops.Internal.print_constr_env curenv sigma cN)
    in
      match (EConstr.kind sigma cM, EConstr.kind sigma cN) with
	| Meta k1, Meta k2 ->
            if Int.equal k1 k2 then substn else
	    let stM,stN = extract_instance_status pb in
            let sigma = 
	      if opt.with_types && flags.check_applied_meta_types then
		let tyM = Typing.meta_type sigma k1 in
		let tyN = Typing.meta_type sigma k2 in
		let l, r = if k2 < k1 then tyN, tyM else tyM, tyN in
		  check_compatibility curenv CUMUL flags substn l r
	      else sigma
	    in
	    if k2 < k1 then sigma,(k1,cN,stN)::metasubst,evarsubst
	    else sigma,(k2,cM,stM)::metasubst,evarsubst
	| Meta k, _
            when not (occur_metavariable sigma k cN) (* helps early trying alternatives *) ->
            let sigma = 
	      if opt.with_types && flags.check_applied_meta_types then
		(try
                   let tyM = Typing.meta_type sigma k in
                   let tyN = get_type_of curenv ~lax:true sigma cN in
                     check_compatibility curenv CUMUL flags substn tyN tyM
		 with RetypeError _ ->
                   (* Renounce, maybe metas/evars prevents typing *) sigma)
	      else sigma
	    in
	    (* Here we check that [cN] does not contain any local variables *)
	    if Int.equal nb 0 then
              sigma,(k,cN,snd (extract_instance_status pb))::metasubst,evarsubst
            else if noccur_between sigma 1 nb cN then
              (sigma,
	      (k,lift (-nb) cN,snd (extract_instance_status pb))::metasubst,
              evarsubst)
	    else error_cannot_unify_local curenv sigma (m,n,cN)
	| _, Meta k
            when not (occur_metavariable sigma k cM) (* helps early trying alternatives *) ->
          let sigma = 
	    if opt.with_types && flags.check_applied_meta_types then
              (try
                 let tyM = get_type_of curenv ~lax:true sigma cM in
                 let tyN = Typing.meta_type sigma k in
                   check_compatibility curenv CUMUL flags substn tyM tyN
               with RetypeError _ ->
                 (* Renounce, maybe metas/evars prevents typing *) sigma)
	    else sigma
	  in
	    (* Here we check that [cM] does not contain any local variables *)
	    if Int.equal nb 0 then
              (sigma,(k,cM,fst (extract_instance_status pb))::metasubst,evarsubst)
	    else if noccur_between sigma 1 nb cM
	    then
              (sigma,(k,lift (-nb) cM,fst (extract_instance_status pb))::metasubst,
              evarsubst)
	    else error_cannot_unify_local curenv sigma (m,n,cM)
	| Evar (evk,_ as ev), Evar (evk',_)
            when not (Evar.Set.mem evk flags.frozen_evars)
              && Evar.equal evk evk' ->
            begin match constr_cmp cv_pb env sigma flags cM cN with
            | Some sigma ->
              sigma, metasubst, evarsubst
            | None ->
	      sigma,metasubst,((curenv,ev,cN)::evarsubst)
            end
	| Evar (evk,_ as ev), _
            when not (Evar.Set.mem evk flags.frozen_evars) 
	      && not (occur_evar sigma evk cN) ->
	    let cmvars = free_rels sigma cM and cnvars = free_rels sigma cN in
	      if Int.Set.subset cnvars cmvars then
		sigma,metasubst,((curenv,ev,cN)::evarsubst)
	      else error_cannot_unify_local curenv sigma (m,n,cN)
	| _, Evar (evk,_ as ev)
            when not (Evar.Set.mem evk flags.frozen_evars)
	      && not (occur_evar sigma evk cM) ->
	    let cmvars = free_rels sigma cM and cnvars = free_rels sigma cN in
	      if Int.Set.subset cmvars cnvars then
		sigma,metasubst,((curenv,ev,cM)::evarsubst)
	      else error_cannot_unify_local curenv sigma (m,n,cN)
	| Sort s1, Sort s2 ->
	    (try 
              let s1 = ESorts.kind sigma s1 in
              let s2 = ESorts.kind sigma s2 in
	       let sigma' = 
		 if pb == CUMUL
		 then Evd.set_leq_sort curenv sigma s1 s2 
		 else Evd.set_eq_sort curenv sigma s1 s2
	       in (sigma', metasubst, evarsubst)
	     with e when CErrors.noncritical e ->
               error_cannot_unify curenv sigma (m,n))

	| Lambda (na,t1,c1), Lambda (_,t2,c2) ->
	    unirec_rec (push (na,t1) curenvnb) CONV {opt with at_top = true}
	      (unirec_rec curenvnb CONV {opt with at_top = true; with_types = false} substn t1 t2) c1 c2
	| Prod (na,t1,c1), Prod (_,t2,c2) ->
	    unirec_rec (push (na,t1) curenvnb) pb {opt with at_top = true}
	      (unirec_rec curenvnb CONV {opt with at_top = true; with_types = false} substn t1 t2) c1 c2
	| LetIn (_,a,_,c), _ -> unirec_rec curenvnb pb opt substn (subst1 a c) cN
	| _, LetIn (_,a,_,c) -> unirec_rec curenvnb pb opt substn cM (subst1 a c)

	(** Fast path for projections. *)
	| Proj (p1,c1), Proj (p2,c2) when Constant.equal
	    (Projection.constant p1) (Projection.constant p2) ->
	  (try unify_same_proj curenvnb cv_pb {opt with at_top = true}
	       substn c1 c2
	   with ex when precatchable_exception ex ->
	     unify_not_same_head curenvnb pb opt substn cM cN)

        (* eta-expansion *)
	| Lambda (na,t1,c1), _ when flags.modulo_eta ->
	    unirec_rec (push (na,t1) curenvnb) CONV {opt with at_top = true} substn
	      c1 (mkApp (lift 1 cN,[|mkRel 1|]))
	| _, Lambda (na,t2,c2) when flags.modulo_eta ->
	    unirec_rec (push (na,t2) curenvnb) CONV {opt with at_top = true} substn
	      (mkApp (lift 1 cM,[|mkRel 1|])) c2

	(* For records *)
	| App (f1, l1), _ when flags.modulo_eta && 
	    (* This ensures cN is an evar, meta or irreducible constant/variable
	       and not a constructor. *)
	    is_eta_constructor_app curenv sigma flags.modulo_delta f1 l1 cN ->
	  (try 
	     let l1', l2' = eta_constructor_app curenv sigma f1 l1 cN in
	     let opt' = {opt with at_top = true; with_cs = false} in
	       Array.fold_left2 (unirec_rec curenvnb CONV opt') substn l1' l2'
	   with ex when precatchable_exception ex ->
	     match EConstr.kind sigma cN with
	     | App(f2,l2) when
		 (isMeta sigma f2 && use_metas_pattern_unification sigma flags nb l2
		  || use_evars_pattern_unification flags && isAllowedEvar sigma flags f2) ->
	       unify_app_pattern false curenvnb pb opt substn cM f1 l1 cN f2 l2
	     | _ -> raise ex)

	| _, App (f2, l2) when flags.modulo_eta && 
	    is_eta_constructor_app curenv sigma flags.modulo_delta f2 l2 cM ->
	  (try 
	     let l2', l1' = eta_constructor_app curenv sigma f2 l2 cM in
	     let opt' = {opt with at_top = true; with_cs = false} in
	       Array.fold_left2 (unirec_rec curenvnb CONV opt') substn l1' l2'
	   with ex when precatchable_exception ex ->
	     match EConstr.kind sigma cM with
	     | App(f1,l1) when 
		 (isMeta sigma f1 && use_metas_pattern_unification sigma flags nb l1
		  || use_evars_pattern_unification flags && isAllowedEvar sigma flags f1) ->
	       unify_app_pattern true curenvnb pb opt substn cM f1 l1 cN f2 l2
	     | _ -> raise ex)

	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
            (try 
	     let opt' = {opt with at_top = true; with_types = false} in
	       Array.fold_left2 (unirec_rec curenvnb CONV {opt with at_top = true})
	       (unirec_rec curenvnb CONV opt'
		(unirec_rec curenvnb CONV opt' substn p1 p2) c1 c2)
                 cl1 cl2
	     with ex when precatchable_exception ex ->
	       reduce curenvnb pb opt substn cM cN)

        | Fix ((ln1,i1),(lna1,tl1,bl1)), Fix ((ln2,i2),(_,tl2,bl2)) when
               Int.equal i1 i2 && Array.equal Int.equal ln1 ln2 ->
            (try
             let opt' = {opt with at_top = true; with_types = false} in
             let curenvnb' = Array.fold_right2 (fun na t -> push (na,t)) lna1 tl1 curenvnb in
               Array.fold_left2 (unirec_rec curenvnb' CONV opt')
               (Array.fold_left2 (unirec_rec curenvnb CONV opt') substn tl1 tl2) bl1 bl2
             with ex when precatchable_exception ex ->
               reduce curenvnb pb opt substn cM cN)

        | CoFix (i1,(lna1,tl1,bl1)), CoFix (i2,(_,tl2,bl2)) when
               Int.equal i1 i2 ->
            (try
             let opt' = {opt with at_top = true; with_types = false} in
             let curenvnb' = Array.fold_right2 (fun na t -> push (na,t)) lna1 tl1 curenvnb in
               Array.fold_left2 (unirec_rec curenvnb' CONV opt')
               (Array.fold_left2 (unirec_rec curenvnb CONV opt') substn tl1 tl2) bl1 bl2
             with ex when precatchable_exception ex ->
               reduce curenvnb pb opt substn cM cN)

	| App (f1,l1), _ when 
	    (isMeta sigma f1 && use_metas_pattern_unification sigma flags nb l1
            || use_evars_pattern_unification flags && isAllowedEvar sigma flags f1) ->
	  unify_app_pattern true curenvnb pb opt substn cM f1 l1 cN cN [||]

	| _, App (f2,l2) when
	    (isMeta sigma f2 && use_metas_pattern_unification sigma flags nb l2
            || use_evars_pattern_unification flags && isAllowedEvar sigma flags f2) ->
	  unify_app_pattern false curenvnb pb opt substn cM cM [||] cN f2 l2

	| App (f1,l1), App (f2,l2) ->
	  unify_app curenvnb pb opt substn cM f1 l1 cN f2 l2
	    
	| App (f1,l1), Proj(p2,c2) ->
	  unify_app curenvnb pb opt substn cM f1 l1 cN cN [||]

	| Proj (p1,c1), App(f2,l2) ->
	  unify_app curenvnb pb opt substn cM cM [||] cN f2 l2

	| _ ->
          unify_not_same_head curenvnb pb opt substn cM cN

  and unify_app_pattern dir curenvnb pb opt (sigma, _, _ as substn) cM f1 l1 cN f2 l2 =
    let f, l, t = if dir then f1, l1, cN else f2, l2, cM in
      match is_unification_pattern curenvnb sigma f (Array.to_list l) t with
      | None ->
	(match EConstr.kind sigma t with
	| App (f',l') -> 
	  if dir then unify_app curenvnb pb opt substn cM f1 l1 t f' l'
	  else unify_app curenvnb pb opt substn t f' l' cN f2 l2
	| Proj _ -> unify_app curenvnb pb opt substn cM f1 l1 cN f2 l2
	| _ -> unify_not_same_head curenvnb pb opt substn cM cN)
      | Some l ->
	solve_pattern_eqn_array curenvnb f l t substn

  and unify_app (curenv, nb as curenvnb) pb opt (sigma, metas, evars as substn : subst0) cM f1 l1 cN f2 l2 =
    try
      let needs_expansion p c' = 
	match EConstr.kind sigma c' with
	| Meta _ -> true
	| Evar _ -> true
	| Const (c, u) -> Constant.equal c (Projection.constant p)
	| _ -> false
      in
      let expand_proj c c' l = 
      	match EConstr.kind sigma c with
      	| Proj (p, t) when not (Projection.unfolded p) && needs_expansion p c' ->
      	  (try destApp sigma (Retyping.expand_projection curenv sigma p t (Array.to_list l))
      	   with RetypeError _ -> (** Unification can be called on ill-typed terms, due
      				     to FO and eta in particular, fail gracefully in that case *)
      	     (c, l))
      	| _ -> (c, l)
      in
      let f1, l1 = expand_proj f1 f2 l1 in
      let f2, l2 = expand_proj f2 f1 l2 in
      let opta = {opt with at_top = true; with_types = false} in
      let optf = {opt with at_top = true; with_types = true} in
      let (f1,l1,f2,l2) = adjust_app_array_size f1 l1 f2 l2 in
	if Array.length l1 == 0 then error_cannot_unify (fst curenvnb) sigma (cM,cN)
	else
	  Array.fold_left2 (unirec_rec curenvnb CONV opta)
	    (unirec_rec curenvnb CONV optf substn f1 f2) l1 l2
    with ex when precatchable_exception ex ->
    try reduce curenvnb pb {opt with with_types = false} substn cM cN
    with ex when precatchable_exception ex ->
    try canonical_projections curenvnb pb opt cM cN substn
    with ex when precatchable_exception ex ->
    expand curenvnb pb {opt with with_types = false} substn cM f1 l1 cN f2 l2

  and unify_same_proj (curenv, nb as curenvnb) cv_pb opt substn c1 c2 =
    let substn = unirec_rec curenvnb CONV opt substn c1 c2 in
      try (* Force unification of the types to fill in parameters *)
	let ty1 = get_type_of curenv ~lax:true sigma c1 in
	let ty2 = get_type_of curenv ~lax:true sigma c2 in
	  unify_0_with_initial_metas substn true curenv cv_pb
	    { flags with modulo_conv_on_closed_terms = Some full_transparent_state;
	      modulo_delta = full_transparent_state;
	      modulo_eta = true;
	      modulo_betaiota = true }
	    ty1 ty2
      with RetypeError _ -> substn

  and unify_not_same_head curenvnb pb opt (sigma, metas, evars as substn : subst0) cM cN =
    try canonical_projections curenvnb pb opt cM cN substn
    with ex when precatchable_exception ex ->
    match constr_cmp cv_pb env sigma flags cM cN with
    | Some sigma -> (sigma, metas, evars)
    | None ->
	try reduce curenvnb pb opt substn cM cN
	with ex when precatchable_exception ex ->
	let (f1,l1) =
	  match EConstr.kind sigma cM with App (f,l) -> (f,l) | _ -> (cM,[||]) in
	let (f2,l2) =
	  match EConstr.kind sigma cN with App (f,l) -> (f,l) | _ -> (cN,[||]) in
	  expand curenvnb pb opt substn cM f1 l1 cN f2 l2

  and reduce curenvnb pb opt (sigma, metas, evars as substn) cM cN =
    if flags.modulo_betaiota && not (subterm_restriction opt flags) then
      let cM' = do_reduce flags.modulo_delta curenvnb sigma cM in
	if not (EConstr.eq_constr sigma cM cM') then
	  unirec_rec curenvnb pb opt substn cM' cN
	else
	  let cN' = do_reduce flags.modulo_delta curenvnb sigma cN in
	    if not (EConstr.eq_constr sigma cN cN') then
	      unirec_rec curenvnb pb opt substn cM cN'
	    else error_cannot_unify (fst curenvnb) sigma (cM,cN)
    else error_cannot_unify (fst curenvnb) sigma (cM,cN)
	    
  and expand (curenv,_ as curenvnb) pb opt (sigma,metasubst,evarsubst as substn : subst0) cM f1 l1 cN f2 l2 =
    let res =
      (* Try full conversion on meta-free terms. *)
      (* Back to 1995 (later on called trivial_unify in 2002), the
	 heuristic was to apply conversion on meta-free (but not
	 evar-free!) terms in all cases (i.e. for apply but also for
	 auto and rewrite, even though auto and rewrite did not use
	 modulo conversion in the rest of the unification
	 algorithm). By compatibility we need to support this
	 separately from the main unification algorithm *)
      (* The exploitation of known metas has been added in May 2007
	 (it is used by apply and rewrite); it might now be redundant
	 with the support for delta-expansion (which is used
	 essentially for apply)... *)
      if subterm_restriction opt flags then None else 
      match flags.modulo_conv_on_closed_terms with
      | None -> None
      | Some convflags ->
      let subst = ((if flags.use_metas_eagerly_in_conv_on_closed_terms then metasubst else ms), (if flags.use_evars_eagerly_in_conv_on_closed_terms then evarsubst else es)) in
      match subst_defined_metas_evars sigma subst cM with
      | None -> (* some undefined Metas in cM *) None
      | Some m1 ->
      match subst_defined_metas_evars sigma subst cN with
      | None -> (* some undefined Metas in cN *) None
      | Some n1 ->
         (* No subterm restriction there, too much incompatibilities *)
	 let sigma =
	   if opt.with_types then
	     try (* Ensure we call conversion on terms of the same type *)
	       let tyM = get_type_of curenv ~lax:true sigma m1 in
	       let tyN = get_type_of curenv ~lax:true sigma n1 in
	       check_compatibility curenv CUMUL flags substn tyM tyN
	     with RetypeError _ ->
	       (* Renounce, maybe metas/evars prevents typing *) sigma
	   else sigma
	 in 
        match infer_conv ~pb ~ts:convflags curenv sigma m1 n1 with
        | Some sigma ->
          Some (sigma, metasubst, evarsubst)
        | None ->
          if is_ground_term sigma m1 && is_ground_term sigma n1 then
            error_cannot_unify curenv sigma (cM,cN)
          else None
    in
      match res with
      | Some substn -> substn
      | None ->
      let cf1 = key_of curenv sigma opt flags f1 and cf2 = key_of curenv sigma opt flags f2 in
	match oracle_order curenv cf1 cf2 with
	| None -> error_cannot_unify curenv sigma (cM,cN)
	| Some true ->
	    (match expand_key flags.modulo_delta curenv sigma cf1 with
	    | Some c ->
		unirec_rec curenvnb pb opt substn
                  (whd_betaiotazeta sigma (mkApp(c,l1))) cN
	    | None ->
		(match expand_key flags.modulo_delta curenv sigma cf2 with
		| Some c ->
		    unirec_rec curenvnb pb opt substn cM
                      (whd_betaiotazeta sigma (mkApp(c,l2)))
		| None ->
		    error_cannot_unify curenv sigma (cM,cN)))
	| Some false ->
	    (match expand_key flags.modulo_delta curenv sigma cf2 with
	    | Some c ->
		unirec_rec curenvnb pb opt substn cM
                  (whd_betaiotazeta sigma (mkApp(c,l2)))
	    | None ->
		(match expand_key flags.modulo_delta curenv sigma cf1 with
		| Some c ->
		    unirec_rec curenvnb pb opt substn
                      (whd_betaiotazeta sigma (mkApp(c,l1))) cN
		| None ->
		    error_cannot_unify curenv sigma (cM,cN)))

  and canonical_projections (curenv, _ as curenvnb) pb opt cM cN (sigma,_,_ as substn) =
    let f1 () =
      if isApp_or_Proj sigma cM then
	let f1l1 = whd_nored_state sigma (cM,Stack.empty) in
	  if is_open_canonical_projection curenv sigma f1l1 then
	    let f2l2 = whd_nored_state sigma (cN,Stack.empty) in
	      solve_canonical_projection curenvnb pb opt cM f1l1 cN f2l2 substn
	  else error_cannot_unify (fst curenvnb) sigma (cM,cN)
      else error_cannot_unify (fst curenvnb) sigma (cM,cN)
    in
      if not opt.with_cs ||
        begin match flags.modulo_conv_on_closed_terms with
        | None -> true
        | Some _ -> subterm_restriction opt flags
        end then
	error_cannot_unify (fst curenvnb) sigma (cM,cN)
      else
	try f1 () with e when precatchable_exception e ->
	  if isApp_or_Proj sigma cN then
	    let f2l2 = whd_nored_state sigma (cN, Stack.empty) in
	      if is_open_canonical_projection curenv sigma f2l2 then
		let f1l1 = whd_nored_state sigma (cM, Stack.empty) in
		  solve_canonical_projection curenvnb pb opt cN f2l2 cM f1l1 substn
	      else error_cannot_unify (fst curenvnb) sigma (cM,cN)
	  else error_cannot_unify (fst curenvnb) sigma (cM,cN)

  and solve_canonical_projection curenvnb pb opt cM f1l1 cN f2l2 (sigma,ms,es) =
    let (ctx,t,c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) =
      try Evarconv.check_conv_record (fst curenvnb) sigma f1l1 f2l2
      with Not_found -> error_cannot_unify (fst curenvnb) sigma (cM,cN)
    in
    if Reductionops.Stack.compare_shape ts ts1 then
      let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
      let (evd,ks,_) =
	List.fold_left
	  (fun (evd,ks,m) b ->
	    if match n with Some n -> Int.equal m n | None -> false then
                (evd,t2::ks, m-1)
            else
              let mv = new_meta () in
              let evd' = meta_declare mv (substl ks b) evd in
	      (evd', mkMeta mv :: ks, m - 1))
	  (sigma,[],List.length bs) bs
      in
      try
      let opt' = {opt with with_types = false} in
      let substn = Reductionops.Stack.fold2
			   (fun s u1 u -> unirec_rec curenvnb pb opt' s u1 (substl ks u))
			   (evd,ms,es) us2 us in
      let substn = Reductionops.Stack.fold2
			   (fun s u1 u -> unirec_rec curenvnb pb opt' s u1 (substl ks u))
			   substn params1 params in
      let substn = Reductionops.Stack.fold2 (fun s u1 u2 -> unirec_rec curenvnb pb opt' s u1 u2) substn ts ts1 in
      let app = mkApp (c, Array.rev_of_list ks) in
      (* let substn = unirec_rec curenvnb pb b false substn t cN in *)
	unirec_rec curenvnb pb opt' substn c1 app
      with Reductionops.Stack.IncompatibleFold2 ->
	error_cannot_unify (fst curenvnb) sigma (cM,cN)
    else error_cannot_unify (fst curenvnb) sigma (cM,cN)
  in
    
  if !debug_unification then Feedback.msg_debug (str "Starting unification");
  let opt = { at_top = conv_at_top; with_types = false; with_cs = true } in
  try
  let res = 
    if subterm_restriction opt flags ||
      occur_meta_or_undefined_evar sigma m || occur_meta_or_undefined_evar sigma n
    then
      None
    else 
      let ans = match flags.modulo_conv_on_closed_terms with
	| Some convflags -> infer_conv ~pb:cv_pb ~ts:convflags env sigma m n
        | _ -> constr_cmp cv_pb env sigma flags m n in
      match ans with
      | Some sigma -> ans
      | None ->
        if (match flags.modulo_conv_on_closed_terms, flags.modulo_delta with
        | Some (cv_id, cv_k), (dl_id, dl_k) ->
          Id.Pred.subset dl_id cv_id && Cpred.subset dl_k cv_k
        | None,(dl_id, dl_k) ->
          Id.Pred.is_empty dl_id && Cpred.is_empty dl_k)
	then error_cannot_unify env sigma (m, n) else None
  in 
    let a = match res with 
    | Some sigma -> sigma, ms, es
    | None -> unirec_rec (env,0) cv_pb opt subst m n in
    if !debug_unification then Feedback.msg_debug (str "Leaving unification with success");
    a
  with e ->
    let e = CErrors.push e in
    if !debug_unification then Feedback.msg_debug (str "Leaving unification with failure");
    iraise e


let unify_0 env sigma = unify_0_with_initial_metas (sigma,[],[]) true env

let left = true
let right = false

let rec unify_with_eta keptside flags env sigma c1 c2 =
(* Question: try whd_all on ci if not two lambdas? *)
  match EConstr.kind sigma c1, EConstr.kind sigma c2 with
  | (Lambda (na,t1,c1'), Lambda (_,t2,c2')) ->
    let env' = push_rel_assum (na,t1) env in
    let sigma,metas,evars = unify_0 env sigma CONV flags t1 t2 in
    let side,(sigma,metas',evars') =
      unify_with_eta keptside flags env' sigma c1' c2'
    in (side,(sigma,metas@metas',evars@evars'))
  | (Lambda (na,t,c1'),_)->
    let env' = push_rel_assum (na,t) env in
    let side = left in (* expansion on the right: we keep the left side *)
      unify_with_eta side flags env' sigma
      c1' (mkApp (lift 1 c2,[|mkRel 1|]))
  | (_,Lambda (na,t,c2')) ->
    let env' = push_rel_assum (na,t) env in
    let side = right in (* expansion on the left: we keep the right side *)
      unify_with_eta side flags env' sigma
      (mkApp (lift 1 c1,[|mkRel 1|])) c2'
  | _ ->
    (keptside,unify_0 env sigma CONV flags c1 c2)
    
(* We solved problems [?n =_pb u] (i.e. [u =_(opp pb) ?n]) and [?n =_pb' u'],
   we now compute the problem on [u =? u'] and decide which of u or u' is kept

   Rem: the upper constraint is lost in case u <= ?n <= u' (and symmetrically
   in the case u' <= ?n <= u)
 *)
    
let merge_instances env sigma flags st1 st2 c1 c2 =
  match (opp_status st1, st2) with
  | (Conv, Conv) ->
      let side = left (* arbitrary choice, but agrees with compatibility *) in
      let (side,res) = unify_with_eta side flags env sigma c1 c2 in
      (side,Conv,res)
  | ((IsSubType | Conv as oppst1),
     (IsSubType | Conv)) ->
    let res = unify_0 env sigma CUMUL flags c2 c1 in
      if eq_instance_constraint oppst1 st2 then (* arbitrary choice *) (left, st1, res)
      else if eq_instance_constraint st2 IsSubType then (left, st1, res)
      else (right, st2, res)
  | ((IsSuperType | Conv as oppst1),
     (IsSuperType | Conv)) ->
    let res = unify_0 env sigma CUMUL flags c1 c2 in
      if eq_instance_constraint oppst1 st2 then (* arbitrary choice *) (left, st1, res)
      else if eq_instance_constraint st2 IsSuperType then (left, st1, res)
      else (right, st2, res)
  | (IsSuperType,IsSubType) ->
    (try (left, IsSubType, unify_0 env sigma CUMUL flags c2 c1)
     with e when CErrors.noncritical e ->
       (right, IsSubType, unify_0 env sigma CUMUL flags c1 c2))
  | (IsSubType,IsSuperType) ->
    (try (left, IsSuperType, unify_0 env sigma CUMUL flags c1 c2)
     with e when CErrors.noncritical e ->
       (right, IsSuperType, unify_0 env sigma CUMUL flags c2 c1))
    
(* Unification
 *
 * Procedure:
 * (1) The function [unify mc wc M N] produces two lists:
 *     (a) a list of bindings Meta->RHS
 *     (b) a list of bindings EVAR->RHS
 *
 * The Meta->RHS bindings cannot themselves contain
 * meta-vars, so they get applied eagerly to the other
 * bindings.  This may or may not close off all RHSs of
 * the EVARs.  For each EVAR whose RHS is closed off,
 * we can just apply it, and go on.  For each which
 * is not closed off, we need to do a mimick step -
 * in general, we have something like:
 *
 *      ?X == (c e1 e2 ... ei[Meta(k)] ... en)
 *
 * so we need to do a mimick step, converting ?X
 * into
 *
 *      ?X -> (c ?z1 ... ?zn)
 *
 * of the proper types.  Then, we can decompose the
 * equation into
 *
 *      ?z1 --> e1
 *          ...
 *      ?zi --> ei[Meta(k)]
 *          ...
 *      ?zn --> en
 *
 * and keep on going.  Whenever we find that a R.H.S.
 * is closed, we can, as before, apply the constraint
 * directly.  Whenever we find an equation of the form:
 *
 *      ?z -> Meta(n)
 *
 * we can reverse the equation, put it into our metavar
 * substitution, and keep going.
 *
 * The most efficient mimick possible is, for each
 * Meta-var remaining in the term, to declare a
 * new EVAR of the same type.  This is supposedly
 * determinable from the clausale form context -
 * we look up the metavar, take its type there,
 * and apply the metavar substitution to it, to
 * close it off.  But this might not always work,
 * since other metavars might also need to be resolved. *)

let applyHead env evd n c  =
  let rec apprec n c cty evd =
    if Int.equal n 0 then
      (evd, c)
    else
      match EConstr.kind evd (whd_all env evd cty) with
      | Prod (_,c1,c2) ->
        let (evd',evar) =
      Evarutil.new_evar env evd ~src:(Loc.tag Evar_kinds.GoalEvar) c1 in
      apprec (n-1) (mkApp(c,[|evar|])) (subst1 evar c2) evd'
      | _ -> user_err Pp.(str "Apply_Head_Then")
  in
    apprec n c (Typing.unsafe_type_of env evd c) evd

let is_mimick_head sigma ts f =
  match EConstr.kind sigma f with
  | Const (c,u) -> not (CClosure.is_transparent_constant ts c)
  | Var id -> not (CClosure.is_transparent_variable ts id)
  | (Rel _|Construct _|Ind _) -> true
  | _ -> false

let try_to_coerce env evd c cty tycon =
  let j = make_judge c cty in
  let (evd',j') = inh_conv_coerce_rigid_to true env evd j tycon in
  let evd' = Evarconv.solve_unif_constraints_with_heuristics env evd' in
  let evd' = Evd.map_metas_fvalue (fun c -> nf_evar evd' c) evd' in
    (evd',j'.uj_val)

let w_coerce_to_type env evd c cty mvty =
  let evd,tycon = pose_all_metas_as_evars env evd mvty in
    try try_to_coerce env evd c cty tycon
    with e when precatchable_exception e ->
    (* inh_conv_coerce_rigid_to should have reasoned modulo reduction
       but there are cases where it though it was not rigid (like in
       fst (nat,nat)) and stops while it could have seen that it is rigid *)
    let cty = Tacred.hnf_constr env evd cty in
      try_to_coerce env evd c cty tycon
	  
let w_coerce env evd mv c =
  let cty = get_type_of env evd c in
  let mvty = Typing.meta_type evd mv in
  w_coerce_to_type env evd c cty mvty

let unify_to_type env sigma flags c status u =
  let sigma, c = refresh_universes (Some false) env sigma c in
  let t = get_type_of env sigma (nf_meta sigma c) in
  let t = nf_betaiota env sigma (nf_meta sigma t) in
    unify_0 env sigma CUMUL flags t u

let unify_type env sigma flags mv status c =
  let mvty = Typing.meta_type sigma mv in
  let mvty = nf_meta sigma mvty in
    unify_to_type env sigma 
      (set_flags_for_type flags)
      c status mvty

(* Move metas that may need coercion at the end of the list of instances *)

let order_metas metas =
  let rec order latemetas = function
  | [] -> List.rev latemetas
  | (_,_,(_,CoerceToType) as meta)::metas ->
    order (meta::latemetas) metas
  | (_,_,(_,_) as meta)::metas ->
    meta :: order latemetas metas
  in order [] metas

(* Solve an equation ?n[x1=u1..xn=un] = t where ?n is an evar *)

let solve_simple_evar_eqn ts env evd ev rhs =
  match solve_simple_eqn (Evarconv.evar_conv_x ts) env evd (None,ev,rhs) with
  | UnifFailure (evd,reason) ->
      error_cannot_unify env evd ~reason (mkEvar ev,rhs);
  | Success evd -> evd

(* [w_merge env sigma b metas evars] merges common instances in metas
   or in evars, possibly generating new unification problems; if [b]
   is true, unification of types of metas is required *)

let w_merge env with_types flags (evd,metas,evars : subst0) =
  let rec w_merge_rec evd metas evars eqns =

    (* Process evars *)
    match evars with
    | (curenv,(evk,_ as ev),rhs)::evars' ->
	if Evd.is_defined evd evk then
	  let v = mkEvar ev in
	  let (evd,metas',evars'') =
	    unify_0 curenv evd CONV flags rhs v in
	  w_merge_rec evd (metas'@metas) (evars''@evars') eqns
    	else begin
	  (* This can make rhs' ill-typed if metas are *)
          let rhs' = subst_meta_instances evd metas rhs in
          match EConstr.kind evd rhs with
	  | App (f,cl) when occur_meta evd rhs' ->
	      if occur_evar evd evk rhs' then
                error_occur_check curenv evd evk rhs';
	      if is_mimick_head evd flags.modulo_delta f then
		let evd' =
		  mimick_undefined_evar evd flags f (Array.length cl) evk in
		  w_merge_rec evd' metas evars eqns
	      else
		let evd' = 
		  let evd', rhs'' = pose_all_metas_as_evars curenv evd rhs' in
		    try solve_simple_evar_eqn flags.modulo_delta_types curenv evd' ev rhs''
		    with Retyping.RetypeError _ ->
		      error_cannot_unify curenv evd' (mkEvar ev,rhs'')
		in w_merge_rec evd' metas evars' eqns
          | _ ->
	      let evd', rhs'' = pose_all_metas_as_evars curenv evd rhs' in
	      let evd' = 
		try solve_simple_evar_eqn flags.modulo_delta_types curenv evd' ev rhs''
		with Retyping.RetypeError _ -> error_cannot_unify curenv evd' (mkEvar ev, rhs'')
	      in
		w_merge_rec evd' metas evars' eqns
	end
    | [] ->

    (* Process metas *)
    match metas with
    | (mv,c,(status,to_type))::metas ->
        let ((evd,c),(metas'',evars'')),eqns =
	  if with_types && to_type != TypeProcessed then
	    begin match to_type with
	    | CoerceToType ->
              (* Some coercion may have to be inserted *)
	      (w_coerce env evd mv c,([],[])),eqns
	    | _ ->
              (* No coercion needed: delay the unification of types *)
	      ((evd,c),([],[])),(mv,status,c)::eqns
	    end
	  else
	    ((evd,c),([],[])),eqns 
	in
	  if meta_defined evd mv then
	    let {rebus=c'},(status',_) = meta_fvalue evd mv in
            let (take_left,st,(evd,metas',evars')) =
              merge_instances env evd flags status' status c' c
	    in
	    let evd' =
              if take_left then evd
              else meta_reassign mv (c,(st,TypeProcessed)) evd
	    in
              w_merge_rec evd' (metas'@metas@metas'') (evars'@evars'') eqns
    	  else
            let evd' =
              if occur_meta_evd evd mv c then
                if isMetaOf evd mv (whd_all env evd c) then evd
                else error_cannot_unify env evd (mkMeta mv,c)
              else
                meta_assign mv (c,(status,TypeProcessed)) evd in
	    w_merge_rec evd' (metas''@metas) evars'' eqns
    | [] ->
	(* Process type eqns *)
	let rec process_eqns failures = function
	  | (mv,status,c)::eqns ->
              (match (try Inl (unify_type env evd flags mv status c)
		      with e when CErrors.noncritical e -> Inr e)
	       with 
	       | Inr e -> process_eqns (((mv,status,c),e)::failures) eqns
	       | Inl (evd,metas,evars) ->
		   w_merge_rec evd metas evars (List.map fst failures @ eqns))
	  | [] -> 
	      (match failures with
	       | [] -> evd
	       | ((mv,status,c),e)::_ -> raise e)
	in process_eqns [] eqns
	      
  and mimick_undefined_evar evd flags hdc nargs sp =
    let ev = Evd.find_undefined evd sp in
    let sp_env = Global.env_of_context (evar_filtered_hyps ev) in
    let (evd', c) = applyHead sp_env evd nargs hdc in
    let (evd'',mc,ec) =
      unify_0 sp_env evd' CUMUL flags
        (get_type_of sp_env evd' c) ev.evar_concl in
    let evd''' = w_merge_rec evd'' mc ec [] in
    if evd' == evd'''
    then Evd.define sp c evd'''
    else Evd.define sp (Evarutil.nf_evar evd''' c) evd''' in

  let check_types evd = 
    let metas = Evd.meta_list evd in
    let eqns = List.fold_left (fun acc (mv, b) ->
      match b with
      | Clval (n, (t, (c, TypeNotProcessed)), v) -> (mv, c, t.rebus) :: acc
      | _ -> acc) [] metas
    in w_merge_rec evd [] [] eqns
  in
  let res =  (* merge constraints *)
    w_merge_rec evd (order_metas metas)
                (* Assign evars in the order of assignments during unification *)
                (List.rev evars) []
  in
  if with_types then check_types res else res

let w_unify_meta_types env ?(flags=default_unify_flags ()) evd =
  let metas,evd = retract_coercible_metas evd in
  w_merge env true flags.merge_unify_flags (evd,metas,[])

(* [w_unify env evd M N]
   performs a unification of M and N, generating a bunch of
   unification constraints in the process.  These constraints
   are processed, one-by-one - they may either generate new
   bindings, or, if there is already a binding, new unifications,
   which themselves generate new constraints.  This continues
   until we get failure, or we run out of constraints.
   [clenv_typed_unify M N clenv] expects in addition that expected
   types of metavars are unifiable with the types of their instances    *)

let head_app sigma m =
  fst (whd_nored_state sigma (m, Stack.empty))

let isEvar_or_Meta sigma c = match EConstr.kind sigma c with
| Evar _ | Meta _ -> true
| _ -> false

let check_types env flags (sigma,_,_ as subst) m n =
  if isEvar_or_Meta sigma (head_app sigma m) then
    unify_0_with_initial_metas subst true env CUMUL
      flags
      (get_type_of env sigma n)
      (get_type_of env sigma m)
  else if isEvar_or_Meta sigma (head_app sigma n) then
    unify_0_with_initial_metas subst true env CUMUL
      flags
      (get_type_of env sigma m)
      (get_type_of env sigma n)
  else subst

let try_resolve_typeclasses env evd flag m n =
  if flag then
    Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~split:false
      ~fail:true env evd
  else evd

let w_unify_core_0 env evd with_types cv_pb flags m n =
  let (mc1,evd') = retract_coercible_metas evd in
  let (sigma,ms,es) = check_types env (set_flags_for_type flags.core_unify_flags) (evd',mc1,[]) m n in
  let subst2 =
     unify_0_with_initial_metas (sigma,ms,es) false env cv_pb
       flags.core_unify_flags m n
  in
  let evd = w_merge env with_types flags.merge_unify_flags subst2 in
  try_resolve_typeclasses env evd flags.resolve_evars m n

let w_typed_unify env evd = w_unify_core_0 env evd true

let w_typed_unify_array env evd flags f1 l1 f2 l2 =
  let f1,l1,f2,l2 = adjust_app_array_size f1 l1 f2 l2 in
  let (mc1,evd') = retract_coercible_metas evd in
  let fold_subst subst m n = unify_0_with_initial_metas subst true env CONV flags.core_unify_flags  m n in
  let subst = fold_subst (evd', [], []) f1 f2 in
  let subst = Array.fold_left2 fold_subst subst l1 l2 in
  let evd = w_merge env true flags.merge_unify_flags subst in
  try_resolve_typeclasses env evd flags.resolve_evars
                          (mkApp(f1,l1)) (mkApp(f2,l2))

(* takes a substitution s, an open term op and a closed term cl
   try to find a subterm of cl which matches op, if op is just a Meta
   FAIL because we cannot find a binding *)

let iter_fail f a =
  let n = Array.length a in
  let rec ffail i =
    if Int.equal i n then user_err Pp.(str "iter_fail")
    else
      try f a.(i)
      with ex when precatchable_exception ex -> ffail (i+1)
  in ffail 0

(* make_abstraction: a variant of w_unify_to_subterm which works on
   contexts, with evars, and possibly with occurrences *)

let indirectly_dependent sigma c d decls =
  not (isVar sigma c) &&
    (* This test is not needed if the original term is a variable, but
       it is needed otherwise, as e.g. when abstracting over "2" in
       "forall H:0=2, H=H:>(0=1+1) -> 0=2." where there is now obvious
       way to see that the second hypothesis depends indirectly over 2 *)
    let open Context.Named.Declaration in
    List.exists (fun d' -> exists (fun c -> Termops.local_occur_var sigma (NamedDecl.get_id d') c) d) decls

let finish_evar_resolution ?(flags=Pretyping.all_and_fail_flags) env current_sigma (pending,c) =
  let sigma = Pretyping.solve_remaining_evars flags env current_sigma pending in
  (sigma, nf_evar sigma c)

let default_matching_core_flags sigma =
  let ts = Names.full_transparent_state in {
  modulo_conv_on_closed_terms = Some empty_transparent_state;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = empty_transparent_state;
  modulo_delta_types = ts;
  check_applied_meta_types = true;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = false;
  frozen_evars = Evar.Map.domain (Evd.undefined_map sigma);
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = false;
}

let default_matching_merge_flags sigma =
  let ts = Names.full_transparent_state in
  let flags = default_matching_core_flags sigma in {
  flags with
    modulo_conv_on_closed_terms = Some ts;
    modulo_delta = ts;
    modulo_betaiota = true;
    modulo_eta = true;
    use_pattern_unification = true;
}

let default_matching_flags sigma =
  let flags = default_matching_core_flags sigma in {
  core_unify_flags = flags;
  merge_unify_flags = default_matching_merge_flags sigma;
  subterm_unify_flags = flags; (* does not matter *)
  resolve_evars = false;
  allow_K_in_toplevel_higher_order_unification = false;
}

(* This supports search of occurrences of term from a pattern *)
(* from_prefix is useful e.g. for subterms in an inductive type: we can say *)
(* "destruct t" and it finds "t u" *)

exception PatternNotFound

let make_pattern_test from_prefix_of_ind is_correct_type env sigma (pending,c) =
  let flags =
    if from_prefix_of_ind then
      let flags = default_matching_flags pending in
      { flags with core_unify_flags = { flags.core_unify_flags with
        modulo_conv_on_closed_terms = Some Names.full_transparent_state;
        restrict_conv_on_strict_subterms = true } }
    else default_matching_flags pending in
  let n = Array.length (snd (decompose_app_vect sigma c)) in
  let matching_fun _ t =
    try
      let t',l2 =
        if from_prefix_of_ind then
          (* We check for fully applied subterms of the form "u u1 .. un" *)
          (* of inductive type knowing only a prefix "u u1 .. ui" *)
          let t,l = decompose_app sigma t in
          let l1,l2 =
            try List.chop n l with Failure _ -> raise (NotUnifiable None) in
          if not (List.for_all (fun c -> Vars.closed0 sigma c) l2) then raise (NotUnifiable None)
          else
            applist (t,l1), l2
        else t, [] in
      let sigma = w_typed_unify env sigma Reduction.CONV flags c t' in
      let ty = Retyping.get_type_of env sigma t in
      if not (is_correct_type ty) then raise (NotUnifiable None);
      Some(sigma, t, l2)
    with
    | PretypeError (_,_,CannotUnify (c1,c2,Some e)) ->
        raise (NotUnifiable (Some (c1,c2,e)))
    (** MS: This is pretty bad, it catches Not_found for example *)
    | e when CErrors.noncritical e -> raise (NotUnifiable None) in
  let merge_fun c1 c2 =
    match c1, c2 with
    | Some (evd,c1,x), Some (_,c2,_) ->
      begin match infer_conv ~pb:CONV env evd c1 c2 with
      | Some evd -> Some (evd, c1, x)
      | None -> raise (NotUnifiable None)
      end
    | Some _, None -> c1
    | None, Some _ -> c2
    | None, None -> None in
  { match_fun = matching_fun; merge_fun = merge_fun;
    testing_state = None; last_found = None },
  (fun test -> match test.testing_state with
  | None -> None
  | Some (sigma,_,l) ->
     let c = applist (local_strong whd_meta sigma c, l) in
     Some (sigma, c))

let make_eq_test env evd c =
  let out cstr =
    match cstr.last_found with None -> None | _ -> Some (cstr.testing_state, c)
  in
  (make_eq_univs_test env evd c, out)

let make_abstraction_core name (test,out) env sigma c ty occs check_occs concl =
  let id =
    let t = match ty with Some t -> t | None -> get_type_of env sigma c in
    let x = id_of_name_using_hdchar (Global.env()) sigma t name in
    let ids = Environ.ids_of_named_context_val (named_context_val env) in
    if name == Anonymous then next_ident_away_in_goal x ids else
    if mem_named_context_val x (named_context_val env) then
      user_err ~hdr:"Unification.make_abstraction_core"
        (str "The variable " ++ Id.print x ++ str " is already declared.")
    else
      x
  in
  let likefirst = clause_with_generic_occurrences occs in
  let mkvarid () = EConstr.mkVar id in
  let compute_dependency _ d (sign,depdecls) =
    let d = map_named_decl EConstr.of_constr d in
    let hyp = NamedDecl.get_id d in
    match occurrences_of_hyp hyp occs with
    | NoOccurrences, InHyp ->
        (push_named_context_val d sign,depdecls)
    | AllOccurrences, InHyp as occ ->
        let occ = if likefirst then LikeFirst else AtOccs occ in
        let newdecl = replace_term_occ_decl_modulo sigma occ test mkvarid d in
        if Context.Named.Declaration.equal (EConstr.eq_constr sigma) d newdecl
           && not (indirectly_dependent sigma c d depdecls)
        then
          if check_occs && not (in_every_hyp occs)
          then raise (PretypeError (env,sigma,NoOccurrenceFound (c,Some hyp)))
          else (push_named_context_val d sign, depdecls)
        else
          (push_named_context_val newdecl sign, newdecl :: depdecls)
    | occ ->
        (* There are specific occurrences, hence not like first *)
        let newdecl = replace_term_occ_decl_modulo sigma (AtOccs occ) test mkvarid d in
        (push_named_context_val newdecl sign, newdecl :: depdecls) in
  try
    let sign,depdecls =
      fold_named_context compute_dependency env
        ~init:(empty_named_context_val,[]) in
    let ccl = match occurrences_of_goal occs with
      | NoOccurrences -> concl
      | occ ->
          let occ = if likefirst then LikeFirst else AtOccs occ in
          replace_term_occ_modulo sigma occ test mkvarid concl
    in
    let lastlhyp =
      if List.is_empty depdecls then None else Some (NamedDecl.get_id (List.last depdecls)) in
    let res = match out test with
    | None -> None
    | Some (sigma, c) -> Some (sigma,c)
    in
    (id,sign,depdecls,lastlhyp,ccl,res)
  with
    SubtermUnificationError e ->
      raise (PretypeError (env,sigma,CannotUnifyOccurrences e))

(** [make_abstraction] is the main entry point to abstract over a term
    or pattern at some occurrences; it returns:
    - the id used for the abstraction
    - the type of the abstraction
    - the declarations from the context which depend on the term or pattern
    - the most recent hyp before which there is no dependency in the term of pattern
    - the abstracted conclusion
    - an evar universe context effect to apply on the goal
    - the term or pattern to abstract fully instantiated
*)

type prefix_of_inductive_support_flag = bool

type abstraction_request =
| AbstractPattern of prefix_of_inductive_support_flag * (types -> bool) * Name.t * (evar_map * constr) * clause * bool
| AbstractExact of Name.t * constr * types option * clause * bool

type 'r abstraction_result =
  Names.Id.t * named_context_val *
    named_declaration list * Names.Id.t option *
    types * (evar_map * constr) option

let make_abstraction env evd ccl abs =
  match abs with
  | AbstractPattern (from_prefix,check,name,c,occs,check_occs) ->
      make_abstraction_core name
        (make_pattern_test from_prefix check env evd c)
        env evd (snd c) None occs check_occs ccl
  | AbstractExact (name,c,ty,occs,check_occs) ->
      make_abstraction_core name
        (make_eq_test env evd c)
        env evd c ty occs check_occs ccl

let keyed_unify env evd kop = 
  if not !keyed_unification then fun cl -> true
  else 
    match kop with 
    | None -> fun _ -> true
    | Some kop ->
      fun cl ->
	let kc = Keys.constr_key (fun c -> EConstr.kind evd c) cl in
	  match kc with
	  | None -> false
	  | Some kc -> Keys.equiv_keys kop kc

(* Tries to find an instance of term [cl] in term [op].
   Unifies [cl] to every subterm of [op] until it finds a match.
   Fails if no match is found *)
let w_unify_to_subterm env evd ?(flags=default_unify_flags ()) (op,cl) =
  let bestexn = ref None in
  let kop = Keys.constr_key (fun c -> EConstr.kind evd c) op in
  let rec matchrec cl =
    let cl = strip_outer_cast evd cl in
    (try
       if closed0 evd cl && not (isEvar evd cl) && keyed_unify env evd kop cl then
       (try
         if !keyed_unification then
           let f1, l1 = decompose_app_vect evd op in
	   let f2, l2 = decompose_app_vect evd cl in
	   w_typed_unify_array env evd flags f1 l1 f2 l2,cl
	 else w_typed_unify env evd CONV flags op cl,cl
       with ex when Pretype_errors.unsatisfiable_exception ex ->
	    bestexn := Some ex; user_err Pp.(str "Unsat"))
       else user_err Pp.(str "Bound 1")
     with ex when precatchable_exception ex ->
       (match EConstr.kind evd cl with
	  | App (f,args) ->
	      let n = Array.length args in
	      assert (n>0);
	      let c1 = mkApp (f,Array.sub args 0 (n-1)) in
	      let c2 = args.(n-1) in
	      (try
		 matchrec c1
	       with ex when precatchable_exception ex ->
		 matchrec c2)
          | Case(_,_,c,lf) -> (* does not search in the predicate *)
	       (try
		 matchrec c
	       with ex when precatchable_exception ex ->
		 iter_fail matchrec lf)
	  | LetIn(_,c1,_,c2) ->
	       (try
		 matchrec c1
	       with ex when precatchable_exception ex ->
		 matchrec c2)

	  | Proj (p,c) -> matchrec c

	  | Fix(_,(_,types,terms)) ->
	       (try
		 iter_fail matchrec types
	       with ex when precatchable_exception ex ->
		 iter_fail matchrec terms)

	  | CoFix(_,(_,types,terms)) ->
	       (try
		 iter_fail matchrec types
	       with ex when precatchable_exception ex ->
		 iter_fail matchrec terms)

          | Prod (_,t,c) ->
	      (try
		 matchrec t
	       with ex when precatchable_exception ex ->
		 matchrec c)

          | Lambda (_,t,c) ->
	      (try
		 matchrec t
	       with ex when precatchable_exception ex ->
		 matchrec c)

          | Cast (_, _, _) (* Is this expected? *)
          | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Const _ | Ind _
            | Construct _ -> user_err Pp.(str "Match_subterm")))
  in
  try matchrec cl
  with ex when precatchable_exception ex ->
    match !bestexn with
    | None -> raise (PretypeError (env,evd,NoOccurrenceFound (op, None)))
    | Some e -> raise e

(* Tries to find all instances of term [cl] in term [op].
   Unifies [cl] to every subterm of [op] and return all the matches.
   Fails if no match is found *)
let w_unify_to_subterm_all env evd ?(flags=default_unify_flags ()) (op,cl) =
  let return a b =
    let (evd,c as a) = a () in
      if List.exists (fun (evd',c') -> EConstr.eq_constr evd' c c') b then b else a :: b
  in
  let fail str _ = user_err (Pp.str str) in
  let bind f g a =
    let a1 = try f a
             with ex
             when precatchable_exception ex -> a
    in try g a1
       with ex
       when precatchable_exception ex -> a1
  in
  let bind_iter f a =
    let n = Array.length a in
    let rec ffail i =
      if Int.equal i n then fun a -> a
      else bind (f a.(i)) (ffail (i+1))
    in ffail 0
  in
  let rec matchrec cl =
    let cl = strip_outer_cast evd cl in
      (bind
	  (if closed0 evd cl
	  then return (fun () -> w_typed_unify env evd CONV flags op cl,cl)
            else fail "Bound 1")
          (match EConstr.kind evd cl with
	    | App (f,args) ->
		let n = Array.length args in
		assert (n>0);
		let c1 = mkApp (f,Array.sub args 0 (n-1)) in
		let c2 = args.(n-1) in
		bind (matchrec c1) (matchrec c2)

            | Case(_,_,c,lf) -> (* does not search in the predicate *)
		bind (matchrec c) (bind_iter matchrec lf)

	    | Proj (p,c) -> matchrec c

	    | LetIn(_,c1,_,c2) ->
		bind (matchrec c1) (matchrec c2)

	    | Fix(_,(_,types,terms)) ->
		bind (bind_iter matchrec types) (bind_iter matchrec terms)

	    | CoFix(_,(_,types,terms)) ->
		bind (bind_iter matchrec types) (bind_iter matchrec terms)

            | Prod (_,t,c) ->
		bind (matchrec t) (matchrec c)

            | Lambda (_,t,c) ->
		bind (matchrec t) (matchrec c)

          | Cast (_, _, _)  -> fail "Match_subterm" (* Is this expected? *)

          | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Const _ | Ind _
            | Construct _ -> fail "Match_subterm"))

  in
  let res = matchrec cl [] in
  match res with
  | [] ->
    raise (PretypeError (env,evd,NoOccurrenceFound (op, None)))
  | _ -> res

let w_unify_to_subterm_list env evd flags hdmeta oplist t =
  List.fold_right
    (fun op (evd,l) ->
      let op = whd_meta evd op in
      if isMeta evd op then
	if flags.allow_K_in_toplevel_higher_order_unification then (evd,op::l)
	else error_abstraction_over_meta env evd hdmeta (destMeta evd op)
      else
        let allow_K = flags.allow_K_in_toplevel_higher_order_unification in
        let flags =
          if unsafe_occur_meta_or_existential op || !keyed_unification then
	    (* This is up to delta for subterms w/o metas ... *)
            flags
          else
            (* up to Nov 2014, unification was bypassed on evar/meta-free terms;
               now it is called in a minimalistic way, at least to possibly
               unify pre-existing non frozen evars of the goal or of the
               pattern *)
          set_no_delta_flags flags in
	let t' = (strip_outer_cast evd op,t) in
        let (evd',cl) =
          try
  	    if is_keyed_unification () then
    	      try (* First try finding a subterm w/o conversion on open terms *)
	        let flags = set_no_delta_open_flags flags in
		w_unify_to_subterm env evd ~flags t'
	      with e ->
		(* If this fails, try with full conversion *)
		w_unify_to_subterm env evd ~flags t'
	    else w_unify_to_subterm env evd ~flags t'
	  with PretypeError (env,_,NoOccurrenceFound _) when
              allow_K ||
                (* w_unify_to_subterm does not go through evars, so
                   the next step, which was already in <= 8.4, is
                   needed at least for compatibility of rewrite *)
                dependent evd op t -> (evd,op)
        in
	  if not allow_K &&
            (* ensure we found a different instance *)
	    List.exists (fun op -> EConstr.eq_constr evd' op cl) l
	  then error_non_linear_unification env evd hdmeta cl
	  else (evd',cl::l))
    oplist
    (evd,[])

let secondOrderAbstraction env evd flags typ (p, oplist) =
  (* Remove delta when looking for a subterm *)
  let flags = { flags with core_unify_flags = flags.subterm_unify_flags } in
  let (evd',cllist) = w_unify_to_subterm_list env evd flags p oplist typ in
  let typp = Typing.meta_type evd' p in
  let evd',(pred,predtyp) = abstract_list_all env evd' typp typ cllist in
  match infer_conv ~pb:CUMUL env evd' predtyp typp with
  | None ->
    error_wrong_abstraction_type env evd'
      (Evd.meta_name evd p) pred typp predtyp;
  | Some evd' ->
  w_merge env false flags.merge_unify_flags
          (evd',[p,pred,(Conv,TypeProcessed)],[])

let secondOrderDependentAbstraction env evd flags typ (p, oplist) =
  let typp = Typing.meta_type evd p in
  let evd, pred = abstract_list_all_with_dependencies env evd typp typ oplist in
  w_merge env false flags.merge_unify_flags
          (evd,[p,pred,(Conv,TypeProcessed)],[])


let secondOrderAbstractionAlgo dep =
  if dep then secondOrderDependentAbstraction else secondOrderAbstraction

let w_unify2 env evd flags dep cv_pb ty1 ty2 =
  let c1, oplist1 = whd_nored_stack evd ty1 in
  let c2, oplist2 = whd_nored_stack evd ty2 in
  match EConstr.kind evd c1, EConstr.kind evd c2 with
    | Meta p1, _ ->
        (* Find the predicate *)
        secondOrderAbstractionAlgo dep env evd flags ty2 (p1, oplist1)
    | _, Meta p2 ->
        (* Find the predicate *)
        secondOrderAbstractionAlgo dep env evd flags ty1 (p2, oplist2)
    | _ -> user_err Pp.(str "w_unify2")

(* The unique unification algorithm works like this: If the pattern is
   flexible, and the goal has a lambda-abstraction at the head, then
   we do a first-order unification.

   If the pattern is not flexible, then we do a first-order
   unification, too.

   If the pattern is flexible, and the goal doesn't have a
   lambda-abstraction head, then we second-order unification. *)

(* We decide here if first-order or second-order unif is used for Apply *)
(* We apply a term of type (ai:Ai)C and try to solve a goal C'          *)
(* The type C is in clenv.templtyp.rebus with a lot of Meta to solve    *)

(* 3-4-99 [HH] New fo/so choice heuristic :
   In case we have to unify (Meta(1) args) with ([x:A]t args')
   we first try second-order unification and if it fails first-order.
   Before, second-order was used if the type of Meta(1) and [x:A]t was
   convertible and first-order otherwise. But if failed if e.g. the type of
   Meta(1) had meta-variables in it. *)
let w_unify env evd cv_pb ?(flags=default_unify_flags ()) ty1 ty2 =
  let hd1,l1 = decompose_app_vect evd (whd_nored evd ty1) in
  let hd2,l2 = decompose_app_vect evd (whd_nored evd ty2) in
  let is_empty1 = Array.is_empty l1 in
  let is_empty2 = Array.is_empty l2 in
    match EConstr.kind evd hd1, not is_empty1, EConstr.kind evd hd2, not is_empty2 with
      (* Pattern case *)
      | (Meta _, true, Lambda _, _ | Lambda _, _, Meta _, true)
	  when Int.equal (Array.length l1) (Array.length l2) ->
	  (try
	      w_typed_unify_array env evd flags hd1 l1 hd2 l2
	    with ex when precatchable_exception ex ->
	      try
		w_unify2 env evd flags false cv_pb ty1 ty2
	      with PretypeError (env,_,NoOccurrenceFound _) as e -> raise e)

      (* Second order case *)
      | (Meta _, true, _, _ | _, _, Meta _, true) ->
	  (try
	      w_unify2 env evd flags false cv_pb ty1 ty2
	    with PretypeError (env,_,NoOccurrenceFound _) as e -> raise e
	      | ex when precatchable_exception ex ->
		  try
		    w_typed_unify_array env evd flags hd1 l1 hd2 l2
		  with ex' when precatchable_exception ex' ->
                    (* Last chance, use pattern-matching with typed
                       dependencies (done late for compatibility) *)
	            try
	              w_unify2 env evd flags true cv_pb ty1 ty2
		    with ex' when precatchable_exception ex' ->
		      raise ex)

      (* General case: try first order *)
      | _ -> w_typed_unify env evd cv_pb flags ty1 ty2

(* Profiling *)

let w_unify env evd cv_pb flags ty1 ty2 =
  w_unify env evd cv_pb ~flags:flags ty1 ty2

let w_unify = 
  if Flags.profile then
    let wunifkey = CProfile.declare_profile "w_unify" in
      CProfile.profile6 wunifkey w_unify
  else w_unify

let w_unify env evd cv_pb ?(flags=default_unify_flags ()) ty1 ty2 =
  w_unify env evd cv_pb flags ty1 ty2
