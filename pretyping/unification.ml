(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Context
open Termops
open Environ
open EConstr
open Vars
open Namegen
open Evd
open Conversion
open Reductionops
open Structures
open Evarutil
open Evardefine
open Evarsolve
open Pretype_errors
open Retyping
open Locus
open Locusops
open Find_subterm

(*******************************************************************)
(* Metamaps *)

(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Int.Set.t }

(* Collects all metavars appearing in a constr *)
let metavars_of c =
  let rec collrec acc c =
    match Constr.kind c with
      | Meta mv -> Int.Set.add mv acc
      | _         -> Constr.fold collrec acc c
  in
  collrec Int.Set.empty (EConstr.Unsafe.to_constr c)

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }

let map_fl f cfl = { cfl with rebus=f cfl.rebus }

(* Status of an instance found by unification wrt to the meta it solves:
  - a supertype of the meta (e.g. the solution to ?X <= T is a supertype of ?X)
  - a subtype of the meta (e.g. the solution to T <= ?X is a supertype of ?X)
  - a term that can be eta-expanded n times while still being a solution
    (e.g. the solution [P] to [?X u v = P u v] can be eta-expanded twice)
*)

type instance_constraint = IsSuperType | IsSubType | Conv

(* Status of the unification of the type of an instance against the type of
     the meta it instantiates:
   - CoerceToType means that the unification of types has not been done
     and that a coercion can still be inserted: the meta should not be
     substituted freely (this happens for instance given via the
     "with" binding clause).
   - TypeProcessed means that the information obtainable from the
     unification of types has been extracted.
   - TypeNotProcessed means that the unification of types has not been
     done but it is known that no coercion may be inserted: the meta
     can be substituted freely.
*)

type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

(* Status of an instance together with the status of its type unification *)

type instance_status = instance_constraint * instance_typing_status

(* Clausal environments *)

type clbinding =
  | Cltyp of Name.t * constr freelisted
  | Clval of Name.t * (constr freelisted * instance_status) * constr freelisted

let map_clb f = function
  | Cltyp (na,cfl) -> Cltyp (na,map_fl f cfl)
  | Clval (na,(cfl1,pb),cfl2) -> Clval (na,(map_fl f cfl1,pb),map_fl f cfl2)

(* name of defined is erased (but it is pretty-printed) *)
let clb_name = function
    Cltyp(na,_) -> (na,false)
  | Clval (na,_,_) -> (na,true)

(***********************)

module Metaset = Int.Set

module Metamap = Int.Map

(**********************************************************)
(* Accessing metas *)

module Meta =
struct

type t = clbinding Metamap.t
type nonrec instance_typing_status = instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

let empty = Metamap.empty

let fold f map accu =
  Metamap.fold (fun mv _ accu -> f mv accu) map accu

let map_metas f metas =
  let map cl = map_clb f cl in
  Metamap.Smart.map map metas

let meta_opt_fvalue0 metas mv =
  match Metamap.find mv metas with
    | Clval(_,b,_) -> Some b
    | Cltyp _ -> None

let meta_opt_fvalue metas mv = match meta_opt_fvalue0 metas mv with
| None -> None
| Some (b, _) -> Some b

let meta_value evd mv = match meta_opt_fvalue evd mv with
| Some body -> body.rebus
| None -> raise Not_found

let meta_ftype metas mv =
  match Metamap.find mv metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b

let meta_handler metas =
  let meta_value mv = match meta_opt_fvalue metas mv with
  | None -> None
  | Some b -> Some b.rebus
  in
  { Reductionops.meta_value }

(* [instance] is used for [res_pf]; the call to [local_strong whd_betaiota]
   has (unfortunately) different subtle side effects:

   - ** Order of subgoals **
     If the lemma is a case analysis with parameters, it will move the
     parameters as first subgoals (e.g. "case H" applied on
     "H:D->A/\B|-C" will present the subgoal |-D first while w/o
     betaiota the subgoal |-D would have come last).

   - ** Betaiota-contraction in statement **
     If the lemma has a parameter which is a function and this
     function is applied in the lemma, then the _strong_ betaiota will
     contract the application of the function to its argument (e.g.
     "apply (H (fun x => x))" in "H:forall f, f 0 = 0 |- 0=0" will
     result in applying the lemma 0=0 in which "(fun x => x) 0" has
     been contracted). A goal to rewrite may then fail or succeed
     differently.

   - ** Naming of hypotheses **
     If a lemma is a function of the form "fun H:(forall a:A, P a)
     => .. F H .." where the expected type of H is "forall b:A, P b",
     then, without reduction, the application of the lemma will
     generate a subgoal "forall a:A, P a" (and intro will use name
     "a"), while with reduction, it will generate a subgoal "forall
     b:A, P b" (and intro will use name "b").

   - ** First-order pattern-matching **
     If a lemma has the type "(fun x => p) t" then rewriting t may fail
     if the type of the lemma is first beta-reduced (this typically happens
     when rewriting a single variable and the type of the lemma is obtained
     by meta_instance (with empty map) which itself calls instance with this
     empty map).
 *)

let meta_instance metas env sigma c =
  (* if s = [] then c else *)
  (* No need to compute contexts under binders as whd_betaiota is local *)
  let metas = meta_handler metas in
  let rec strongrec t = EConstr.map sigma strongrec (whd_betaiota ~metas env sigma t) in
  strongrec c

let meta_type metas env evd mv =
  let ty =
    try meta_ftype metas mv
    with Not_found -> anomaly (str "unknown meta ?" ++ str (Nameops.string_of_meta mv) ++ str ".") in
  if Metaset.is_empty ty.freemetas then ty.rebus
  else meta_instance metas env evd ty.rebus

let meta_declare mv v ?(name=Anonymous) metas =
  let metas = Metamap.add mv (Cltyp(name,mk_freelisted v)) metas in
  metas

(* If the meta is defined then forget its name *)
let meta_name metas mv =
  try fst (clb_name (Metamap.find mv metas)) with Not_found -> Anonymous

let evar_source_of_meta mv metas =
  match meta_name metas mv with
  | Anonymous -> Loc.tag Evar_kinds.GoalEvar
  | Name id   -> Loc.tag @@ Evar_kinds.VarInstance id

let use_meta_source metas evd mv v =
  let v = EConstr.Unsafe.to_constr v in
  match Constr.kind v with
  | Evar (evk,_) ->
    begin match Evd.find_undefined evd evk with
    | evi ->
      begin match evar_source evi with
      | None, Evar_kinds.GoalEvar -> Evd.update_source evd evk (evar_source_of_meta mv metas)
      | _ -> evd
      end
    | exception Not_found -> evd
    end
  | _ -> evd

let meta_assign0 mv (v, pb) metas evd =
  let modify _ = function
  | Cltyp (na, ty) -> Clval (na, (mk_freelisted v, pb), ty)
  | _ -> anomaly ~label:"meta_assign" (Pp.str "already defined.")
  in
  let metas = Metamap.modify mv modify metas in
  let evd = use_meta_source metas evd mv v in
  evd, metas

let meta_assign mv (v, pb) metas evd =
  meta_assign0 mv (v, (Conv, pb)) metas evd

let meta_merge metas sigma =
  Metamap.fold Metamap.add metas sigma

let meta_reassign mv (v, pb) metas =
  let modify _ = function
  | Clval(na, _, ty) -> Clval (na, (mk_freelisted v, pb), ty)
  | _ -> anomaly ~label:"meta_reassign" (Pp.str "not yet defined.")
  in
  Metamap.modify mv modify metas

let map_metas_fvalue f metas =
  let map = function
  | Clval(id,(c,s),typ) -> Clval(id,(mk_freelisted (f c.rebus),s),typ)
  | x -> x
  in
  Metamap.Smart.map map metas

let retract_coercible_metas metas =
  let mc = ref [] in
  let map n v = match v with
  | Clval (na, (b, (Conv, CoerceToType as s)), typ) ->
    let () = mc := (n, b.rebus, s) :: !mc in
    Cltyp (na, typ)
  | v -> v
  in
  let metas = Metamap.Smart.mapi map metas in
  !mc, metas

let pr_metaset metas =
  let open Nameops in
  str "[" ++ pr_sequence pr_meta (Metaset.elements metas) ++ str "]"

let pr_instance_status (sc,typ) =
  begin match sc with
  | IsSubType -> str " [or a subtype of it]"
  | IsSuperType -> str " [or a supertype of it]"
  | Conv -> mt ()
  end ++
  begin match typ with
  | CoerceToType -> str " [up to coercion]"
  | TypeNotProcessed -> mt ()
  | TypeProcessed -> str " [type is checked]"
  end

let pr_metamap env sigma metas =
  let open Nameops in
  let print_constr = Termops.Internal.print_kconstr in
  let pr_name = function
      Name id -> str"[" ++ Id.print id ++ str"]"
    | _ -> mt() in
  let pr_meta_binding = function
    | (mv,Cltyp (na,b)) ->
        hov 0
          (pr_meta mv ++ pr_name na ++ str " : " ++
           print_constr env sigma b.rebus ++ fnl ())
    | (mv,Clval(na,(b,s),t)) ->
        hov 0
          (pr_meta mv ++ pr_name na ++ str " := " ++
           print_constr env sigma b.rebus ++
           str " : " ++ print_constr env sigma t.rebus ++
           spc () ++ pr_instance_status s ++ fnl ())
  in
  prlist pr_meta_binding (Metamap.bindings metas)

end

type metabinding = (metavariable * EConstr.constr * (instance_constraint * instance_typing_status))

type subst0 = {
  subst_sigma : evar_map;
  subst_metas : metabinding list;
  subst_metam : clbinding Metamap.t;
  subst_evars : ((Environ.env * int) * EConstr.existential * EConstr.t) list;
}

let push_sigma sigma s = {
  subst_sigma = sigma;
  subst_metas = s.subst_metas;
  subst_metam = s.subst_metam;
  subst_evars = s.subst_evars;
}

let push_metas sigma m s = {
  subst_sigma = sigma;
  subst_metas = m :: s.subst_metas;
  subst_metam = s.subst_metam;
  subst_evars = s.subst_evars;
}

let push_evars sigma e s = {
  subst_sigma = sigma;
  subst_metas = s.subst_metas;
  subst_metam = s.subst_metam;
  subst_evars = e :: s.subst_evars;
}

module NamedDecl = Context.Named.Declaration

let { Goptions.get = is_keyed_unification } =
  Goptions.declare_bool_option_and_ref
    ~key:["Keyed";"Unification"]
    ~value:false
    ()

let debug_tactic_unification = CDebug.create ~name:"tactic-unification" ()

let occur_meta_or_undefined_evar evd c =
  (* This is performance-critical. Using the evar-insensitive API changes the
     resulting heuristic. *)
  let c = EConstr.Unsafe.to_constr c in
  let rec occrec c = match Constr.kind c with
    | Meta _ -> raise Occur
    | Evar (ev,args) ->
      let EvarInfo evi = Evd.find evd ev in
        (match evar_body evi with
        | Evar_defined c ->
            occrec (EConstr.Unsafe.to_constr c); SList.Skip.iter occrec args
        | Evar_empty -> raise Occur)
    | _ -> Constr.iter occrec c
  in try occrec c; false with Occur | Not_found -> true

let whd_meta ~metas sigma c = match EConstr.kind sigma c with
  | Meta p ->
    (try Meta.meta_value metas p with Not_found -> c)
    (* Not recursive, for some reason *)
  | _ -> c

let occur_meta_evd ~metas sigma mv c =
  let rec occrec c =
    (* Note: evars are not instantiated by terms with metas *)
    let c = whd_meta ~metas sigma c in
    match EConstr.kind sigma c with
    | Meta mv' when Int.equal mv mv' -> raise Occur
    | Evar (_, args) -> SList.Skip.iter occrec args
    | _ -> EConstr.iter sigma occrec c
  in try occrec c; false with Occur -> true

(* if lname_typ is [xn,An;..;x1,A1] and l is a list of terms,
   gives [x1:A1]..[xn:An]c' such that c converts to ([x1:A1]..[xn:An]c' l) *)

let abstract_scheme env evd c l lname_typ =
  let mkLambda_name env (n,a,b) =
    mkLambda (map_annot (named_hd env evd a) n, a, b)
  in
  List.fold_left2
    (fun (t,evd) (locc,a) (na,ta) ->
       let na = match EConstr.kind evd a with Var id -> {na with binder_name=Name id} | _ -> na in
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
  let ctxt,_ = whd_decompose_prod_n env evd (List.length l) typ in
  let l_with_all_occs = List.map (function a -> (LikeFirst,a)) l in
  let p,evd = abstract_scheme env evd c l_with_all_occs ctxt in
  let evd,typp =
    try
      let c = EConstr.it_mkLambda (EConstr.Vars.lift (List.length ctxt) c) ctxt in
      Typing.recheck_against env evd c p
    with
    | UserError _ ->
        error_cannot_find_well_typed_abstraction env evd p l None
    | Type_errors.TypeError (env',x) ->
        (* FIXME: plug back the typing information *)
        error_cannot_find_well_typed_abstraction env evd p l None
    | Pretype_errors.PretypeError (env',evd,e) ->
        error_cannot_find_well_typed_abstraction env evd p l (Some (env',e)) in
  evd,(p,typp)

let set_occurrences_of_last_arg n =
  Evarconv.AtOccurrences AllOccurrences ::
    List.tl (List.init n (fun _ -> Evarconv.Unspecified Abstraction.Abstract))

let occurrence_test env sigma c1 c2 =
  match EConstr.eq_constr_universes env sigma c1 c2 with
  | None -> false, sigma
  | Some cstr ->
     try true, Evd.add_universe_constraints sigma cstr
     with UniversesDiffer | UGraph.UniverseInconsistency _ -> false, sigma

let abstract_list_all_with_dependencies env evd typ c l =
  let (evd, ev) = new_evar env evd typ in
  let evd,ev' = evar_absorb_arguments env evd (destEvar evd ev) l in
  let n = List.length l in
  let () = assert (n <= SList.length (snd ev')) in
  let argoccs = set_occurrences_of_last_arg n in
  let evd,b =
    if occur_meta evd c then evd, false
    else
    Evarconv.second_order_matching
      (Evarconv.default_flags_of TransparentState.empty)
      env evd ev' (occurrence_test, argoccs) c in
  if b then
    let p = nf_evar evd ev in
      evd, p
  else error_cannot_find_well_typed_abstraction env evd
    c l None

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

let pose_all_metas_as_evars ~metas env evd t =
  let evdref = ref evd in
  let metas = ref metas in
  let rec aux t = match EConstr.kind !evdref t with
  | Meta mv ->
      (match Meta.meta_opt_fvalue !metas mv with
       | Some {rebus=c;freemetas=mvs} ->
         let c = if Metaset.is_empty mvs then c else aux c in
         metas := Meta.meta_reassign mv (c,(Conv,TypeNotProcessed)) !metas;
         c
       | None ->
        let {rebus=ty;freemetas=mvs} = Meta.meta_ftype !metas mv in
        let ty = if Metaset.is_empty mvs then ty else aux ty in
        let ty = nf_betaiota env !evdref ty in
        let src = Meta.evar_source_of_meta mv !metas in
        let evd, ev = Evarutil.new_evar env !evdref ~src ty in
        let evd, nmetas = Meta.meta_assign mv (ev, TypeNotProcessed) !metas evd in
        let () = evdref := evd in
        let () = metas := nmetas in
        ev)
  | _ ->
      EConstr.map !evdref aux t in
  let c = aux t in
  (* side-effect *)
  (!evdref, !metas, c)

let solve_pattern_eqn_array (env,nb) f l c (subst : subst0) =
  let sigma = subst.subst_sigma in
  let metas = subst.subst_metam in
  match EConstr.kind sigma f with
    | Meta k ->
        (* We enforce that the Meta does not depend on the [nb]
           extra assumptions added by unification to the context *)
        let env' = pop_rel_context nb env in
        let sigma, metas, c = pose_all_metas_as_evars ~metas env' sigma c in
        let c = solve_pattern_eqn env sigma l c in
        let pb = (Conv,TypeNotProcessed) in
          if noccur_between sigma 1 nb c then
            let subst = push_metas sigma  (k, lift (-nb) c, pb) subst in
            { subst with subst_metam = metas }
          else
            let l = List.map of_alias l in
            error_cannot_unify_local env sigma (applist (f, l),c,c)
    | Evar ev ->
        let env' = pop_rel_context nb env in
        let sigma, metas, c = pose_all_metas_as_evars ~metas env' sigma c in
        let subst = push_evars sigma ((env,nb),ev,solve_pattern_eqn env sigma l c) subst in
        { subst with subst_metam = metas }
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
  modulo_conv_on_closed_terms : TransparentState.t option;
    (* What this flag controls was activated with all constants transparent, *)
    (* even for auto, since Coq V5.10 *)

  use_metas_eagerly_in_conv_on_closed_terms : bool;
    (* This refinement of the conversion on closed terms is activable *)
    (* (and activated for apply, rewrite but not auto since Feb 2008 for 8.2) *)

  use_evars_eagerly_in_conv_on_closed_terms : bool;

  modulo_delta : TransparentState.t;
    (* This controls which constants are unfoldable; this is on for apply *)
    (* (but not simple apply) since Feb 2008 for 8.2 *)

  modulo_delta_types : TransparentState.t;

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

  allowed_evars : AllowedEvars.t;
    (* Evars that are allowed to be instantiated *)
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
  let ts = TransparentState.full in {
  modulo_conv_on_closed_terms = Some ts;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = ts;
  modulo_delta_types = ts;
  check_applied_meta_types = true;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  allowed_evars = AllowedEvars.all;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = true;
  modulo_eta = true;
 }

let ts_var_full =
  let open TransparentState in
  { tr_var = Id.Pred.full; tr_cst = Cpred.empty; tr_prj = PRpred.empty }

(* Default flag for first-order or second-order unification of a type *)
(* against another type (e.g. apply)                                  *)
(* We set all conversion flags (no flag should be modified anymore)   *)
let default_unify_flags () =
  let flags = default_core_unify_flags () in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = ts_var_full };
  allow_K_in_toplevel_higher_order_unification = false; (* Why not? *)
  resolve_evars = false
}

let set_no_delta_core_flags flags = { flags with
  modulo_conv_on_closed_terms = None;
  modulo_delta = TransparentState.empty;
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
  modulo_delta = TransparentState.empty;
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
  modulo_delta = TransparentState.empty;
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

let allow_new_evars sigma =
  let undefined = Evd.undefined_map sigma in
  AllowedEvars.from_pred (fun evk -> not (Evar.Map.mem evk undefined))

(* Default flags for looking for subterms in elimination tactics *)
(* Not used in practice at the current date, to the exception of *)
(* allow_K) because only closed terms are involved in *)
(* induction/destruct/case/elim and w_unify_to_subterm_list does not *)
(* call w_unify for induction/destruct/case/elim  (13/6/2011) *)
let elim_core_flags sigma = { (default_core_unify_flags ()) with
  modulo_betaiota = false;
  allowed_evars = allow_new_evars sigma;
}

let elim_flags_evars sigma =
  let flags = elim_core_flags sigma in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = TransparentState.empty };
  allow_K_in_toplevel_higher_order_unification = true;
  resolve_evars = false
}

let elim_flags () = elim_flags_evars Evd.empty

let elim_no_delta_core_flags () = { (elim_core_flags Evd.empty) with
  modulo_delta = TransparentState.empty;
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


(* [unfold_projection_under_eta env ts n c] checks if [c] is the eta
   expanded, folded primitive projection of name [n] and unfolds the primitive
   projection. It respects projection transparency of [ts]. *)
let unfold_projection_under_eta env ts n c =
  let unfold_projection env ts p r c =
    if TransparentState.is_transparent_projection ts (Projection.repr p) then
      Some (Constr.mkProj (Projection.unfold p, r, c))
    else None
  in
  let rec go c lams =
    match Constr.kind c with
    | Lambda (b, t, c) -> go c ((b,t)::lams)
    | Proj (p, r, c) when QConstant.equal env n (Projection.constant p) ->
      let c = unfold_projection env ts p r c in
      begin
        match c with
        | None -> None
        | Some c ->
          let f c (b,t) = Constr.mkLambda (b,t,c) in
          Some (List.fold_left f c lams)
      end
    | _ -> None
  in
  go c []


type key =
  | IsKey of CClosure.table_key
  | IsProj of Projection.t * ERelevance.t * EConstr.constr

let expand_table_key ~metas ts env sigma args = function
  | ConstKey (c, _ as cst) ->
      if Structures.PrimitiveProjections.is_transparent_constant ts c then
        match constant_value_in env cst with
        (* If we are unfolding a compatibility constant we want to return the
            unfolded primitive projection directly since we would like to pretend
            that the compatibility constant itself does not count as an unfolding
            (delta) step. *)
        | def ->
        let unf = unfold_projection_under_eta env ts c def in
        Some (EConstr.of_constr @@ Option.default def unf, args)
        | exception NotEvaluableConst (HasRules (u, b, r)) ->
        begin try
          let metas = Meta.meta_handler metas in
          let sk = Stack.( append_app args empty ) in
          let rhs, stack = Reductionops.apply_rules
            (whd_betaiota_deltazeta_for_iota_state ts ~metas env sigma) env sigma (EInstance.make u) r sk
          in
          let args' = Stack.list_of_app_stack stack
            |> (function Some l -> l | None -> assert false)
            |> Array.of_list in
          Some (rhs, args')
        with PatternFailure -> None
        (* TODO: try unfold fix *)
        end
        | exception NotEvaluableConst _ -> None
      else None
  | VarKey id -> (try named_body id env |> Option.map (fun c -> (EConstr.of_constr c, args)) with Not_found -> None)
  | RelKey _ -> None

let unfold_projection env p r stk =
  let s = Stack.Proj (p,r) in
  s :: stk

let expand_key ~metas ts env sigma args = function
  | Some (IsKey k) -> (expand_table_key ~metas ts env sigma args k)
  | Some (IsProj (p, r, c)) ->
    let metas = Meta.meta_handler metas in
    let red = Stack.zip sigma (whd_betaiota_deltazeta_for_iota_state ts ~metas env sigma
                               (c, unfold_projection env p r []))
    in if EConstr.eq_constr sigma (EConstr.mkProj (p, r, c)) red then None else Some (red, args)
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
  | Const (cst, u) when is_transparent env (Evaluable.EvalConstRef cst) &&
      (Structures.PrimitiveProjections.is_transparent_constant flags.modulo_delta cst
       || PrimitiveProjections.mem cst) ->
      let u = EInstance.kind sigma u in
      Some (IsKey (ConstKey (cst, u)))
  | Var id when is_transparent env (Evaluable.EvalVarRef id) &&
      TransparentState.is_transparent_variable flags.modulo_delta id ->
    Some (IsKey (VarKey id))
  | Proj (p, r, c) when Names.Projection.unfolded p
    || (is_transparent env (Evaluable.EvalProjectionRef (Projection.repr p)) &&
       (TransparentState.is_transparent_projection flags.modulo_delta (Projection.repr p))) ->
    Some (IsProj (p, r, c))
  | _ -> None


let translate_key = function
  | ConstKey (cst,u) -> Some (Conv_oracle.EvalConstRef cst)
  | VarKey id -> Some (Conv_oracle.EvalVarRef id)
  | RelKey _ -> None

let translate_key = function
  | IsKey k -> translate_key k
  | IsProj (p, _, _) -> Some (Conv_oracle.EvalProjectionRef (Projection.repr p))

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
        | IsProj (p, _, _), IsKey (ConstKey (p',_))
          when Environ.QConstant.equal env (Projection.constant p) p' ->
          Some (not (Projection.unfolded p))
        | IsKey (ConstKey (p,_)), IsProj (p', _, _)
          when Environ.QConstant.equal env p (Projection.constant p') ->
          Some (Projection.unfolded p')
        | _ ->
          Some (Conv_oracle.oracle_order
                  (Environ.oracle env) false (translate_key k1) (translate_key k2))

let is_rigid_head sigma flags t =
  match EConstr.kind sigma t with
  | Const (cst,u) -> not (Structures.PrimitiveProjections.is_transparent_constant flags.modulo_delta cst)
  | Ind (i,u) -> true
  | Construct _ | Int _ | Float _ | String _ | Array _ -> true
  | Fix _ | CoFix _ -> true
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Cast (_, _, _) | Prod _
    | Lambda _ | LetIn _ | App (_, _) | Case _
    | Proj _ -> false (* Why aren't Prod, Sort rigid heads ? *)

let constr_cmp pb env sigma flags ?nargs t u =
  let cstrs =
    if pb == Conversion.CONV then EConstr.eq_constr_universes env sigma ?nargs t u
    else EConstr.leq_constr_universes env sigma ?nargs t u
  in
  match cstrs with
  | Some cstrs ->
      begin try Some (Evd.add_universe_constraints sigma cstrs)
      with UGraph.UniverseInconsistency _ -> None
      | Evd.UniversesDiffer ->
        if is_rigid_head sigma flags t then
          try Some (Evd.add_universe_constraints sigma (UnivProblem.Set.force cstrs))
          with UGraph.UniverseInconsistency _ -> None
        else None
      end
  | None ->
    None

let do_reduce ~metas ts (env, nb) sigma c =
  let metas = Meta.meta_handler metas in
  Stack.zip sigma (whd_betaiota_deltazeta_for_iota_state ~metas
                  ts env sigma (c, Stack.empty))

let is_evar_allowed flags evk =
  AllowedEvars.mem flags.allowed_evars evk

let isAllowedEvar sigma flags c = match EConstr.kind sigma c with
  | Evar (evk,_) -> is_evar_allowed flags evk
  | _ -> false


let subst_defined_metas_evars sigma (bl,el) c =
  (* This seems to be performance-critical, and using the
     evar-insensitive primitives blow up the time passed in this
     function. *)
  let c = EConstr.Unsafe.to_constr c in
  let rec substrec c = match Constr.kind c with
    | Meta i ->
      let select (j,_,_) = Int.equal i j in
      substrec (EConstr.Unsafe.to_constr (pi2 (List.find select bl)))
    | Evar (evk,args) ->
      let eq c1 c2 = Constr.equal c1 (EConstr.Unsafe.to_constr c2) in
      let select (_,(evk',args'),_) = Evar.equal evk evk' && SList.equal eq args args' in
      begin match List.find select el with
      | (_, _, c) -> substrec (EConstr.Unsafe.to_constr c)
      | exception Not_found ->
        let c = EConstr.(Unsafe.to_constr (whd_evar sigma (of_constr c))) in
        Constr.map substrec c
      end
    | _ -> Constr.map substrec c
  in try Some (EConstr.of_constr (substrec c)) with Not_found -> None

let check_compatibility env pbty flags subst tyM tyN =
  let sigma = subst.subst_sigma in
  match subst_defined_metas_evars sigma (subst.subst_metas, []) tyM with
  | None -> sigma
  | Some m ->
  match subst_defined_metas_evars sigma (subst.subst_metas, []) tyN with
  | None -> sigma
  | Some n ->
    if is_ground_term sigma m && is_ground_term sigma n then
      match infer_conv ~pb:pbty ~ts:flags.modulo_delta_types env sigma m n with
      | Some sigma -> sigma
      | None -> error_cannot_unify env sigma (m,n)
    else sigma

let check_compatibility_ustate env pbty flags subst tyM tyN =
  let sigma = subst.subst_sigma in
  match subst_defined_metas_evars sigma (subst.subst_metas, []) tyM with
  | None -> UnivProblem.Set.empty
  | Some m ->
  match subst_defined_metas_evars sigma (subst.subst_metas, []) tyN with
  | None -> UnivProblem.Set.empty
  | Some n ->
    if is_ground_term sigma m && is_ground_term sigma n then
      match infer_conv_ustate ~pb:pbty ~ts:flags.modulo_delta_types env sigma m n with
      | Some uprob -> uprob
      | None -> error_cannot_unify env sigma (m,n)
    else UnivProblem.Set.empty

let rec is_neutral env sigma ts t =
  let (f, l) = decompose_app sigma t in
    match EConstr.kind sigma f with
    | Const (c, u) ->
      not (Environ.evaluable_constant c env) ||
      not (is_transparent env (Evaluable.EvalConstRef c)) ||
      not (Structures.PrimitiveProjections.is_transparent_constant ts c)
    | Var id ->
      not (Environ.evaluable_named id env) ||
      not (is_transparent env (Evaluable.EvalVarRef id)) ||
      not (TransparentState.is_transparent_variable ts id)
    | Rel n -> true
    | Evar _ | Meta _ -> true
    | Case (_, _, _, _, _, c, _) -> is_neutral env sigma ts c
    | Proj (p, _, c) -> is_neutral env sigma ts c
    | Lambda _ | LetIn _ | Construct _ | CoFix _ | Int _ | Float _ | String _ | Array _ -> false
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
          let (_, projs, _, _) = info.(i) in
          Array.length projs == Array.length l1 - mib.Declarations.mind_nparams ->
        (* Check that the other term is neutral *)
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
        let l2 = Array.map (fun (p,_) ->
            mkApp (mkConstU (Projection.Repr.constant p,u), arg)) projs in
        l1', l2
      | _ -> assert false)
  | _ -> assert false

let get_type_of_with_metas ~metas ?lax env sigma c =
  let metas n =
    try Some (Meta.meta_ftype metas n).rebus
    with Not_found -> None
  in
  Retyping.get_type_of ~metas ?lax env sigma c

let expand_projection_with_metas ~metas env sigma pr c args =
  let ty = get_type_of_with_metas ~metas ~lax:true env sigma c in
  let (i,u), ind_args =
    try Inductiveops.find_mrectype env sigma ty
    with Not_found -> error_disallowed_sprop env sigma (* dummy, caught immediately *)
  in
    mkApp (mkConstU (Projection.constant pr,u),
           Array.of_list (ind_args @ (c :: args)))

(* If the terms are irrelevant, check that they have the same type. *)
let careful_infer_conv ~pb ~ts env sigma m n =
  if Retyping.is_term_irrelevant env sigma m &&
     Retyping.is_term_irrelevant env sigma n
  then
    let tm = Retyping.get_type_of env sigma m in
    let tn = Retyping.get_type_of env sigma n in
    Option.bind (infer_conv ~pb:CONV ~ts env sigma tm tn)
      (fun sigma -> infer_conv ~pb ~ts env sigma m n)
  else infer_conv ~pb ~ts env sigma m n

type maybe_ground = Ground | NotGround | Unknown

let error_cannot_unify_local env sigma (m, n, p) =
  error_cannot_unify_local env sigma (fst m, fst n, p)

let fast_occur_meta_or_undefined_evar sigma (c, gnd) = match gnd with
| Unknown -> occur_meta_or_undefined_evar sigma c
| Ground -> false
| NotGround -> true

let rec unify_0_with_initial_metas (subst : subst0) conv_at_top env cv_pb flags m n =
  let mk_expand_subst substn =
    let metasubst = if flags.use_metas_eagerly_in_conv_on_closed_terms then substn.subst_metas else subst.subst_metas in
    let evarsubst = if flags.use_evars_eagerly_in_conv_on_closed_terms then substn.subst_evars else subst.subst_evars in
    (metasubst, evarsubst)
  in
  let rec unirec_rec (curenv,nb as curenvnb) pb opt (substn : subst0) ?(nargs=0) curm curn =
    let { subst_sigma = sigma; subst_metas = metasubst; subst_evars = evarsubst } = substn in
    let cM = Evarutil.whd_head_evar sigma curm
    and cN = Evarutil.whd_head_evar sigma curn in
    let () =
      debug_tactic_unification (fun () ->
          Termops.Internal.print_constr_env curenv sigma cM ++ strbrk" ~= " ++
          Termops.Internal.print_constr_env curenv sigma cN)
    in
      match (EConstr.kind sigma cM, EConstr.kind sigma cN) with
        | Meta k1, Meta k2 ->
            if Int.equal k1 k2 then substn else
            let stM,stN = extract_instance_status pb in
            let sigma =
              if opt.with_types && flags.check_applied_meta_types then
                let tyM = Meta.meta_type substn.subst_metam curenv sigma k1 in
                let tyN = Meta.meta_type substn.subst_metam curenv sigma k2 in
                let l, r = if k2 < k1 then tyN, tyM else tyM, tyN in
                  check_compatibility curenv CUMUL flags substn l r
              else sigma
            in
            if k2 < k1 then push_metas sigma (k1, cN, stN) substn
            else push_metas sigma (k2, cM, stM) substn
        | Meta k, _
            when not (occur_metavariable sigma k cN) (* helps early trying alternatives *) ->
            let sigma =
              if opt.with_types && flags.check_applied_meta_types then
                (try
                   let tyM = Meta.meta_type substn.subst_metam curenv sigma k in
                   let tyN = get_type_of_with_metas ~metas:substn.subst_metam curenv ~lax:true sigma cN in
                     check_compatibility curenv CUMUL flags substn tyN tyM
                 with RetypeError _ ->
                   (* Renounce, maybe metas/evars prevents typing *) sigma)
              else sigma
            in
            (* Here we check that [cN] does not contain any local variables *)
            if Int.equal nb 0 then
              push_metas sigma (k, cN, snd (extract_instance_status pb)) substn
            else if noccur_between sigma 1 nb cN then
              push_metas sigma
                (k, lift (-nb) cN, snd (extract_instance_status pb)) substn
            else error_cannot_unify_local curenv sigma (m,n,cN)
        | _, Meta k
            when not (occur_metavariable sigma k cM) (* helps early trying alternatives *) ->
          let sigma =
            if opt.with_types && flags.check_applied_meta_types then
              (try
                 let tyM = get_type_of_with_metas ~metas:substn.subst_metam curenv ~lax:true sigma cM in
                 let tyN = Meta.meta_type substn.subst_metam curenv sigma k in
                   check_compatibility curenv CUMUL flags substn tyM tyN
               with RetypeError _ ->
                 (* Renounce, maybe metas/evars prevents typing *) sigma)
            else sigma
          in
            (* Here we check that [cM] does not contain any local variables *)
            if Int.equal nb 0 then
              push_metas sigma (k, cM, fst (extract_instance_status pb)) substn
            else if noccur_between sigma 1 nb cM
            then
              push_metas sigma (k, lift (-nb) cM, fst (extract_instance_status pb)) substn
            else error_cannot_unify_local curenv sigma (m,n,cM)
        | Evar (evk,_ as ev), Evar (evk',_)
            when is_evar_allowed flags evk
              && Evar.equal evk evk' ->
            begin match constr_cmp cv_pb env sigma flags cM cN with
            | Some sigma ->
              push_sigma sigma substn
            | None ->
              push_evars sigma (curenvnb, ev, cN) substn
            end
        | Evar (evk,_ as ev), _
            when is_evar_allowed flags evk
              && not (occur_evar sigma evk cN) ->
            let cmvars = free_rels sigma cM and cnvars = free_rels sigma cN in
              if Int.Set.subset cnvars cmvars then
                push_evars sigma (curenvnb, ev, cN) substn
              else error_cannot_unify_local curenv sigma (m,n,cN)
        | _, Evar (evk,_ as ev)
            when is_evar_allowed flags evk
              && not (occur_evar sigma evk cM) ->
            let cmvars = free_rels sigma cM and cnvars = free_rels sigma cN in
              if Int.Set.subset cmvars cnvars then
                push_evars sigma (curenvnb, ev, cM) substn
              else error_cannot_unify_local curenv sigma (m,n,cN)
        | Sort s1, Sort s2 ->
            (try
               let sigma' =
                 if pb == CUMUL
                 then Evd.set_leq_sort sigma s1 s2
                 else Evd.set_eq_sort sigma s1 s2
               in push_sigma sigma' substn
             with e when CErrors.noncritical e ->
               error_cannot_unify curenv sigma (fst m,fst n))

        | Lambda (na,t1,c1), Lambda (__,t2,c2) ->
            unirec_rec (push (na,t1) curenvnb) CONV {opt with at_top = true}
              (unirec_rec curenvnb CONV {opt with at_top = true; with_types = false} substn t1 t2) c1 c2
        | Prod (na,t1,c1), Prod (_,t2,c2) ->
            unirec_rec (push (na,t1) curenvnb) pb {opt with at_top = true}
              (unirec_rec curenvnb CONV {opt with at_top = true; with_types = false} substn t1 t2) c1 c2
        | LetIn (_,a,_,c), _ -> unirec_rec curenvnb pb opt substn (subst1 a c) cN
        | _, LetIn (_,a,_,c) -> unirec_rec curenvnb pb opt substn cM (subst1 a c)

        (* Fast path for projections. *)
        | Proj (p1,_,c1), Proj (p2,_,c2) when Environ.QConstant.equal env
            (Projection.constant p1) (Projection.constant p2) ->
          (try unify_same_proj curenvnb cv_pb {opt with at_top = true}
               substn c1 c2
           with ex when precatchable_exception ex ->
             unify_not_same_head curenvnb pb opt substn ~nargs cM cN)

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
             let opt' = {opt with at_top = true; with_cs = false} in
             let substn = check_type_eta_constructor_app curenvnb opt' substn cM cN in
             let sigma = substn.subst_sigma in
             let l1', l2' = eta_constructor_app curenv sigma f1 l1 cN in
             Array.fold_left2 (unirec_rec curenvnb CONV opt' ~nargs:0) substn l1' l2'
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
             let opt' = {opt with at_top = true; with_cs = false} in
             let substn = check_type_eta_constructor_app curenvnb opt' substn cN cM in
             let sigma = substn.subst_sigma in
             let l2', l1' = eta_constructor_app curenv sigma f2 l2 cM in
             Array.fold_left2 (unirec_rec curenvnb CONV opt' ~nargs:0) substn l1' l2'
           with ex when precatchable_exception ex ->
             match EConstr.kind sigma cM with
             | App(f1,l1) when
                 (isMeta sigma f1 && use_metas_pattern_unification sigma flags nb l1
                  || use_evars_pattern_unification flags && isAllowedEvar sigma flags f1) ->
               unify_app_pattern true curenvnb pb opt substn cM f1 l1 cN f2 l2
             | _ -> raise ex)

        | Case (ci1, u1, pms1, p1, iv1, c1, cl1), Case (ci2, u2, pms2, (p2,_), iv2, c2, cl2) ->
            (try
             let () = if not (QInd.equal curenv ci1.ci_ind ci2.ci_ind) then error_cannot_unify curenv sigma (cM,cN) in
             let opt' = {opt with at_top = true; with_types = false} in
             let substn = Array.fold_left2 (unirec_rec curenvnb CONV ~nargs:0 opt') substn pms1 pms2 in
             let (ci1, _, _, (p1,_), _, c1, cl1) = EConstr.annotate_case env sigma (ci1, u1, pms1, p1, iv1, c1, cl1) in
             let unif opt substn (ctx1, c1) (_, c2) =
               let curenvnb' = List.fold_right (fun decl (env, n) -> push_rel decl env, n + 1) ctx1 curenvnb in
               unirec_rec curenvnb' CONV opt' substn c1 c2
             in
             let substn = unif opt' substn p1 p2 in
             let substn = unirec_rec curenvnb CONV opt' substn c1 c2 in
             Array.fold_left2 (unif {opt with at_top = true}) substn cl1 cl2
             with ex when precatchable_exception ex ->
               reduce curenvnb pb opt substn cM cN)

        | Fix ((ln1,i1),(lna1,tl1,bl1)), Fix ((ln2,i2),(_,tl2,bl2)) when
               Int.equal i1 i2 && Array.equal Int.equal ln1 ln2 ->
            (try
             let opt' = {opt with at_top = true; with_types = false} in
             let curenvnb' = Array.fold_right2 (fun na t -> push (na,t)) lna1 tl1 curenvnb in
               Array.fold_left2 (unirec_rec curenvnb' CONV opt' ~nargs:0)
               (Array.fold_left2 (unirec_rec curenvnb CONV opt' ~nargs:0) substn tl1 tl2) bl1 bl2
             with ex when precatchable_exception ex ->
               reduce curenvnb pb opt substn cM cN)

        | CoFix (i1,(lna1,tl1,bl1)), CoFix (i2,(_,tl2,bl2)) when
               Int.equal i1 i2 ->
            (try
             let opt' = {opt with at_top = true; with_types = false} in
             let curenvnb' = Array.fold_right2 (fun na t -> push (na,t)) lna1 tl1 curenvnb in
               Array.fold_left2 (unirec_rec curenvnb' CONV opt' ~nargs:0)
               (Array.fold_left2 (unirec_rec curenvnb CONV opt' ~nargs:0) substn tl1 tl2) bl1 bl2
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

        | App (f1,l1), Proj(p2,_,c2) ->
          unify_app curenvnb pb opt substn cM f1 l1 cN cN [||]

        | Proj (p1,_,c1), App(f2,l2) ->
          unify_app curenvnb pb opt substn cM cM [||] cN f2 l2

        | _ ->
          unify_not_same_head curenvnb pb opt substn ~nargs cM cN

  and check_type_eta_constructor_app (env,nb as curenvnb) opt (substn : subst0) other term =
    let sigma = substn.subst_sigma in
    let metas = substn.subst_metam in
    let  (((_, i as ind), j), u) =
      EConstr.destConstruct sigma (fst (decompose_app sigma other))
    in
    (* ensure that we only eta expand if we are at the same inductive
       (we accept that univs params and indices may be different) *)
    let fail () =
      error_cannot_unify env sigma (other, term)
    in
    let tterm = try get_type_of_with_metas ~metas ~lax:true env sigma term
      with RetypeError _ -> fail ()
    in
    let tterm' = Reductionops.whd_all ~metas:(Meta.meta_handler metas) env sigma tterm in
     match EConstr.kind sigma (fst (decompose_app sigma tterm')) with
      | Ind (ind',_) when QInd.equal env ind ind' -> substn
      | _ ->
        let tother = try get_type_of_with_metas ~metas ~lax:true env sigma other
          with RetypeError _ ->
            fail ()
        in
        unirec_rec curenvnb CONV opt ~nargs:0 substn tother tterm

  and unify_app_pattern dir curenvnb pb opt substn cM f1 l1 cN f2 l2 =
    let sigma = substn.subst_sigma in
    let f, l, t = if dir then f1, l1, cN else f2, l2, cM in
      match is_unification_pattern curenvnb sigma f (Array.to_list l) t with
      | None ->
        (match EConstr.kind sigma t with
        | App (f',l') ->
          if dir then unify_app curenvnb pb opt substn cM f1 l1 t f' l'
          else unify_app curenvnb pb opt substn t f' l' cN f2 l2
        | Proj _ -> unify_app curenvnb pb opt substn cM f1 l1 cN f2 l2
        | _ ->
          (* XXX nargs could be better? *)
          unify_not_same_head curenvnb pb opt substn ~nargs:0 cM cN)
      | Some l ->
        solve_pattern_eqn_array curenvnb f l t substn

  and unify_app (curenv, nb as curenvnb) pb opt (substn : subst0) cM f1 l1 cN f2 l2 =
    let sigma = substn.subst_sigma in
    try
      let needs_expansion p c' =
        match EConstr.kind sigma c' with
        | Meta _ -> true
        | Evar _ -> true
        | Const (c, u) -> Environ.QConstant.equal env c (Projection.constant p)
        | _ -> false
      in
      let expand_proj c c' l =
        match EConstr.kind sigma c with
        | Proj (p, _, t) when not (Projection.unfolded p) && needs_expansion p c' ->
          (try destApp sigma (expand_projection_with_metas ~metas:substn.subst_metam curenv sigma p t (Array.to_list l))
           with RetypeError _ -> (* Unification can be called on ill-typed terms, due
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
          Array.fold_left2 (unirec_rec curenvnb CONV opta ~nargs:0)
            (unirec_rec curenvnb CONV optf substn f1 f2 ~nargs:(Array.length l1)) l1 l2
    with ex when precatchable_exception ex ->
    try reduce curenvnb pb {opt with with_types = false} substn cM cN
    with ex when precatchable_exception ex ->
    try canonical_projections curenvnb pb opt cM cN substn
    with ex when precatchable_exception ex ->
    expand curenvnb pb {opt with with_types = false} substn cM f1 l1 cN f2 l2

  and unify_same_proj (curenv, nb as curenvnb) cv_pb opt substn c1 c2 =
    let substn = unirec_rec curenvnb CONV opt substn c1 c2 in
    let metas = substn.subst_metam in
      try (* Force unification of the types to fill in parameters *)
        let ty1 = get_type_of_with_metas ~metas curenv ~lax:true substn.subst_sigma c1 in
        let ty2 = get_type_of_with_metas ~metas curenv ~lax:true substn.subst_sigma c2 in
          unify_0_with_initial_metas substn true curenv cv_pb
            { flags with modulo_conv_on_closed_terms = Some TransparentState.full;
              modulo_delta = TransparentState.full;
              modulo_eta = true;
              modulo_betaiota = true }
            (ty1, Unknown) (ty2, Unknown)
      with RetypeError _ -> substn

  and unify_not_same_head curenvnb pb opt (substn : subst0) ~nargs cM cN =
    let sigma = substn.subst_sigma in
    try canonical_projections curenvnb pb opt cM cN substn
    with ex when precatchable_exception ex ->
    match constr_cmp cv_pb env sigma flags ~nargs cM cN with
    | Some sigma -> push_sigma sigma substn
    | None ->
        try reduce curenvnb pb opt substn cM cN
        with ex when precatchable_exception ex ->
        let (f1,l1) =
          match EConstr.kind sigma cM with App (f,l) -> (f,l) | _ -> (cM,[||]) in
        let (f2,l2) =
          match EConstr.kind sigma cN with App (f,l) -> (f,l) | _ -> (cN,[||]) in
          expand curenvnb pb opt substn cM f1 l1 cN f2 l2

  and reduce curenvnb pb opt substn cM cN =
    let sigma = substn.subst_sigma in
    let metas = substn.subst_metam in
    if flags.modulo_betaiota && not (subterm_restriction opt flags) then
      let cM' = do_reduce ~metas flags.modulo_delta curenvnb sigma cM in
        if not (EConstr.eq_constr sigma cM cM') then
          unirec_rec curenvnb pb opt substn cM' cN
        else
          let cN' = do_reduce ~metas flags.modulo_delta curenvnb sigma cN in
            if not (EConstr.eq_constr sigma cN cN') then
              unirec_rec curenvnb pb opt substn cM cN'
            else error_cannot_unify (fst curenvnb) sigma (cM,cN)
    else error_cannot_unify (fst curenvnb) sigma (cM,cN)

  and expand (curenv,_ as curenvnb) pb opt (substn : subst0) cM f1 l1 cN f2 l2 =
    let sigma = substn.subst_sigma in
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
      let subst = mk_expand_subst substn in
      match subst_defined_metas_evars sigma subst cM with
      | None -> (* some undefined Metas in cM *) None
      | Some m1 ->
      match subst_defined_metas_evars sigma subst cN with
      | None -> (* some undefined Metas in cN *) None
      | Some n1 ->
        (* No subterm restriction there, too much incompatibilities
           don't care about universes from comparing the types
        *)
         let _ : UnivProblem.Set.t =
           if opt.with_types then
             try (* Ensure we call conversion on terms of the same type *)
               let tyM = get_type_of curenv ~lax:true sigma m1 in
               let tyN = get_type_of curenv ~lax:true sigma n1 in
               check_compatibility_ustate curenv CUMUL flags substn tyM tyN
             with RetypeError _ ->
               (* Renounce, maybe metas/evars prevents typing *) UnivProblem.Set.empty
           else UnivProblem.Set.empty
         in
        match infer_conv_ustate ~pb ~ts:convflags curenv sigma m1 n1 with
        | Some uprob ->
          begin match Evd.add_universe_constraints sigma uprob with
          | sigma -> Some (push_sigma sigma substn)
          | exception (UGraph.UniverseInconsistency _ | UniversesDiffer) -> None
          end
        | None ->
          if is_ground_term sigma m1 && is_ground_term sigma n1 then
            error_cannot_unify curenv sigma (cM,cN)
          else None
    in
      match res with
      | Some substn -> substn
      | None ->
      let metas = substn.subst_metam in
      let cf1 = key_of curenv sigma opt flags f1 and cf2 = key_of curenv sigma opt flags f2 in
        match oracle_order curenv cf1 cf2 with
        | None -> error_cannot_unify curenv sigma (cM,cN)
        | Some true ->
            (match expand_key ~metas flags.modulo_delta curenv sigma l1 cf1 with
            | Some c_l1 ->
              let metas = Meta.meta_handler metas in
                unirec_rec curenvnb pb opt substn
                  (whd_betaiotazeta ~metas curenv sigma (mkApp c_l1)) cN
            | None ->
                (match expand_key ~metas flags.modulo_delta curenv sigma l2 cf2 with
                | Some c_l2 ->
                  let metas = Meta.meta_handler metas in
                    unirec_rec curenvnb pb opt substn cM
                      (whd_betaiotazeta ~metas curenv sigma (mkApp c_l2))
                | None ->
                    error_cannot_unify curenv sigma (cM,cN)))
        | Some false ->
            (match expand_key ~metas flags.modulo_delta curenv sigma l2 cf2 with
            | Some c_l2 ->
              let metas = Meta.meta_handler metas in
                unirec_rec curenvnb pb opt substn cM
                  (whd_betaiotazeta ~metas curenv sigma (mkApp c_l2))
            | None ->
                (match expand_key ~metas flags.modulo_delta curenv sigma l1 cf1 with
                | Some c_l1 ->
                  let metas = Meta.meta_handler metas in
                    unirec_rec curenvnb pb opt substn
                      (whd_betaiotazeta ~metas curenv sigma (mkApp c_l1)) cN
                | None ->
                    error_cannot_unify curenv sigma (cM,cN)))

  and canonical_projections (curenv, _ as curenvnb) pb opt cM cN substn =
    let sigma = substn.subst_sigma in
    let metas = substn.subst_metam in
    let f1 () =
      if isApp_or_Proj sigma cM then
          if CanonicalSolution.is_open_canonical_projection ~metas:(Meta.meta_handler metas) curenv sigma cM then
            solve_canonical_projection curenvnb pb opt cM cN substn
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
              if CanonicalSolution.is_open_canonical_projection ~metas:(Meta.meta_handler metas) curenv sigma cN then
                solve_canonical_projection curenvnb pb opt cN cM substn
              else error_cannot_unify (fst curenvnb) sigma (cM,cN)
          else error_cannot_unify (fst curenvnb) sigma (cM,cN)

  and solve_canonical_projection curenvnb pb opt cM cN substn =
    let sigma = substn.subst_sigma in
    let metas = substn.subst_metam in
    let f1l1 = whd_nored_state ~metas:(Meta.meta_handler metas) (fst curenvnb) sigma (cM,Stack.empty) in
    let f2l2 = whd_nored_state ~metas:(Meta.meta_handler metas) (fst curenvnb) sigma (cN,Stack.empty) in
    let (sigma,t,c,bs,(params,params1),(us,us2),(ts,ts1),c1,(n,t2)) =
      let metas mv = match Metamap.find mv metas with
      | Cltyp (_, b) -> Some b.rebus
      | Clval (_, _, b) -> Some b.rebus
      | exception Not_found -> None
      in
      try Evarconv.check_conv_record (fst curenvnb) sigma (Evarconv.decompose_proj ~metas (fst curenvnb) sigma f1l1) f2l2
      with Not_found -> error_cannot_unify (fst curenvnb) sigma (cM,cN)
    in
    if Reductionops.Stack.compare_shape ts ts1 then
      let (metas,ks,_) =
        List.fold_left
          (fun (metas,ks,m) b ->
            if match n with Some n -> Int.equal m n | None -> false then
                (metas,t2::ks, m-1)
            else
              let mv = new_meta () in
              let metas = Meta.meta_declare mv (substl ks b) metas in
              (metas, mkMeta mv :: ks, m - 1))
          (metas,[],List.length bs) bs
      in
      let substn = push_sigma sigma substn in
      let substn = { substn with subst_metam = metas } in
      try
      let opt' = {opt with with_types = false} in
      let fold u1 u s = unirec_rec curenvnb pb opt' s u1 (substl ks u) in
      let foldl acc l1 l2 =
        try List.fold_right2 fold l1 l2 acc
        with Invalid_argument _ -> assert false (* check_conv_record ensures lengths coincide *)
      in
      let substn = foldl substn us2 us in
      let substn = match params1 with None -> substn | Some params1 -> foldl substn params1 params in
      let substn = Reductionops.Stack.fold2 (fun s u1 u2 -> unirec_rec curenvnb pb opt' s u1 u2) substn ts ts1 in
      let app = mkApp (c, Array.rev_of_list ks) in
      (* let substn = unirec_rec curenvnb pb b false substn t cN in *)
        unirec_rec curenvnb pb opt' substn c1 app
      with Reductionops.Stack.IncompatibleFold2 ->
        error_cannot_unify (fst curenvnb) sigma (cM,cN)
    else error_cannot_unify (fst curenvnb) sigma (cM,cN)
  in

  let sigma = subst.subst_sigma in
  debug_tactic_unification (fun () ->
      str "Starting unification:" ++ spc() ++
      Termops.Internal.print_constr_env env sigma (fst m) ++ strbrk" ~= " ++
      Termops.Internal.print_constr_env env sigma (fst n));

  let opt = { at_top = conv_at_top; with_types = false; with_cs = true } in
  try
  let res =
    if subterm_restriction opt flags ||
      fast_occur_meta_or_undefined_evar sigma m || fast_occur_meta_or_undefined_evar sigma n
    then
      None
    else
      let (m, _) = m in
      let (n, _) = n in
      let ans = match flags.modulo_conv_on_closed_terms with
        | Some convflags -> careful_infer_conv ~pb:cv_pb ~ts:convflags env sigma m n
        | _ -> constr_cmp cv_pb env sigma flags m n in
      match ans with
      | Some sigma -> ans
      | None ->
        if (match flags.modulo_conv_on_closed_terms, flags.modulo_delta with
        | Some cv, dl ->
          let open TransparentState in
          Id.Pred.subset dl.tr_var cv.tr_var && Cpred.subset dl.tr_cst cv.tr_cst
        | None, dl -> TransparentState.is_empty dl)
        then error_cannot_unify env sigma (m, n) else None
  in
    let a = match res with
    | Some sigma -> push_sigma sigma subst
    | None -> unirec_rec (env,0) cv_pb opt subst (fst m) (fst n) in
    debug_tactic_unification (fun () -> str "Leaving unification with success");
    a
  with e ->
    let e = Exninfo.capture e in
    debug_tactic_unification (fun () -> str "Leaving unification with failure");
    Exninfo.iraise e

let unify_0 ~metas env sigma pb flags c1 c2 =
  unify_0_with_initial_metas { subst_sigma = sigma; subst_metas = []; subst_evars = []; subst_metam = metas } true env pb flags (c1, Unknown) (c2, Unknown)

let left = true
let right = false

let rec unify_with_eta ~metas keptside flags env sigma c1 c2 =
(* Question: try whd_all on ci if not two lambdas? *)
  match EConstr.kind sigma c1, EConstr.kind sigma c2 with
  | (Lambda (na,t1,c1'), Lambda (_,t2,c2')) ->
    let env' = push_rel_assum (na,t1) env in
    let substn = unify_0 ~metas env sigma CONV flags t1 t2 in
    let { subst_sigma = sigma; subst_metas = metas; subst_evars = evars; subst_metam = metas0 } = substn in
    let side, { subst_sigma = sigma; subst_metas = metas'; subst_evars = evars'; subst_metam = metas0 } =
      unify_with_eta ~metas:metas0 keptside flags env' sigma c1' c2'
    in (side, { subst_sigma = sigma; subst_metas = metas@metas'; subst_evars = evars@evars'; subst_metam = metas0 })
  | (Lambda (na,t,c1'),_)->
    let env' = push_rel_assum (na,t) env in
    let side = left in (* expansion on the right: we keep the left side *)
      unify_with_eta ~metas side flags env' sigma
      c1' (mkApp (lift 1 c2,[|mkRel 1|]))
  | (_,Lambda (na,t,c2')) ->
    let env' = push_rel_assum (na,t) env in
    let side = right in (* expansion on the left: we keep the right side *)
      unify_with_eta ~metas side flags env' sigma
      (mkApp (lift 1 c1,[|mkRel 1|])) c2'
  | _ ->
    (keptside, unify_0 ~metas env sigma CONV flags c1 c2)

(* We solved problems [?n =_pb u] (i.e. [u =_(opp pb) ?n]) and [?n =_pb' u'],
   we now compute the problem on [u =? u'] and decide which of u or u' is kept

   Rem: the upper constraint is lost in case u <= ?n <= u' (and symmetrically
   in the case u' <= ?n <= u)
 *)

let eq_instance_constraint (c1 : instance_constraint) c2 = c1 == c2

let merge_instances ~metas env sigma flags st1 st2 c1 c2 =
  match (opp_status st1, st2) with
  | (Conv, Conv) ->
      let side = left (* arbitrary choice, but agrees with compatibility *) in
      let (side,res) = unify_with_eta ~metas side flags env sigma c1 c2 in
      (side,Conv,res)
  | ((IsSubType | Conv as oppst1),
     (IsSubType | Conv)) ->
    let res = unify_0 ~metas env sigma CUMUL flags c2 c1 in
      if eq_instance_constraint oppst1 st2 then (* arbitrary choice *) (left, st1, res)
      else if eq_instance_constraint st2 IsSubType then (left, st1, res)
      else (right, st2, res)
  | ((IsSuperType | Conv as oppst1),
     (IsSuperType | Conv)) ->
    let res = unify_0 ~metas env sigma CUMUL flags c1 c2 in
      if eq_instance_constraint oppst1 st2 then (* arbitrary choice *) (left, st1, res)
      else if eq_instance_constraint st2 IsSuperType then (left, st1, res)
      else (right, st2, res)
  | (IsSuperType,IsSubType) ->
    (try (left, IsSubType, unify_0 ~metas env sigma CUMUL flags c2 c1)
     with e when CErrors.noncritical e ->
       (right, IsSubType, unify_0 ~metas env sigma CUMUL flags c1 c2))
  | (IsSubType,IsSuperType) ->
    (try (left, IsSuperType, unify_0 ~metas env sigma CUMUL flags c1 c2)
     with e when CErrors.noncritical e ->
       (right, IsSuperType, unify_0 ~metas env sigma CUMUL flags c2 c1))

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
 * is not closed off, we need to do a mimic step -
 * in general, we have something like:
 *
 *      ?X == (c e1 e2 ... ei[Meta(k)] ... en)
 *
 * so we need to do a mimic step, converting ?X
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
 * The most efficient mimic possible is, for each
 * Meta-var remaining in the term, to declare a
 * new EVAR of the same type.  This is supposedly
 * determinable from the clausale form context -
 * we look up the metavar, take its type there,
 * and apply the metavar substitution to it, to
 * close it off.  But this might not always work,
 * since other metavars might also need to be resolved. *)

let applyHead ~metas env evd c cl =
  let rec apprec c cl cty evd =
    match cl with
    | [] -> (evd, c)
    | a::cl ->
      match EConstr.kind evd (whd_all ~metas:(Meta.meta_handler metas) env evd cty) with
      | Prod ({binder_name},c1,c2) ->
        let src =
          match EConstr.kind evd a with
          | Meta mv -> Meta.evar_source_of_meta mv metas
          | _ ->
            (* Does not matter, the evar will be later instantiated by [a] *)
            Loc.tag Evar_kinds.InternalHole in
        let (evd,evar) = Evarutil.new_evar env evd ~src c1 in
        apprec (mkApp(c,[|evar|])) cl (subst1 evar c2) evd
      | _ -> user_err Pp.(str "Apply_Head_Then")
  in
  let evd, t = Typing.type_of env evd c in
  apprec c (Array.to_list cl) t evd

let is_mimick_head sigma ts f =
  match EConstr.kind sigma f with
  | Const (c,u) -> not (Structures.PrimitiveProjections.is_transparent_constant ts c)
  | Var id -> not (TransparentState.is_transparent_variable ts id)
  | (Rel _|Construct _|Ind _) -> true
  | _ -> false

let try_to_coerce ~metas env evd c cty tycon =
  let j = make_judge c cty in
  let (evd',j',_trace) = Coercion.inh_conv_coerce_rigid_to ~program_mode:false ~resolve_tc:true env evd j tycon in
  let evd' = Evarconv.solve_unif_constraints_with_heuristics env evd' in
  let metas = Meta.map_metas_fvalue (fun c -> nf_evar evd' c) metas in
  (evd', metas, j'.uj_val)

let w_coerce_to_type ~metas env evd c cty mvty =
  let evd, metas, tycon = pose_all_metas_as_evars ~metas env evd mvty in
    try try_to_coerce ~metas env evd c cty tycon
    with e when precatchable_exception e ->
    (* inh_conv_coerce_rigid_to should have reasoned modulo reduction
       but there are cases where it though it was not rigid (like in
       fst (nat,nat)) and stops while it could have seen that it is rigid *)
    let cty = Tacred.hnf_constr env evd cty in
    try_to_coerce ~metas env evd c cty tycon

let w_coerce ~metas env evd mv c =
  let cty = get_type_of env evd c in
  let mvty = Meta.meta_type metas env evd mv in
  w_coerce_to_type ~metas env evd c cty mvty

let nf_meta ~metas env sigma c =
  let freemetas = metavars_of c in
  if Metaset.is_empty freemetas then c else Meta.meta_instance metas env sigma c

let unify_to_type ~metas env sigma flags c status u =
  let sigma, c = refresh_universes ~status:Evd.univ_flexible ~onlyalg:true (Some false) env sigma c in
  let t = get_type_of_with_metas ~metas env sigma (nf_meta ~metas env sigma c) in
  let t = nf_betaiota env sigma (nf_meta ~metas env sigma t) in
  unify_0 ~metas env sigma CUMUL flags t u

let unify_type ~metas env sigma flags mv status c =
  let mvty = Meta.meta_type metas env sigma mv in
  let mvty = nf_meta ~metas env sigma mvty in
  unify_to_type ~metas env sigma
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

let solve_simple_evar_eqn flags env evd ev rhs =
  match solve_simple_eqn Evarconv.evar_unify flags env evd (None,ev,rhs) with
  | UnifFailure (evd,reason) ->
      error_cannot_unify env evd ~reason (mkEvar ev,rhs);
  | Success evd -> evd

(* [w_merge env sigma b metas evars] merges common instances in metas
   or in evars, possibly generating new unification problems; if [b]
   is true, unification of types of metas is required *)

let w_merge env with_types flags (substn : subst0) =
  let eflags = Evarconv.default_flags_of flags.modulo_delta_types in
  let rec w_merge_rec metas0 evd metas evars eqns =

    (* Process evars *)
    match evars with
    | ((curenv,nb),(evk,_ as ev),rhs)::evars' ->
        if Evd.is_defined evd evk then
          let v = mkEvar ev in
          let { subst_sigma = evd; subst_metas = metas'; subst_evars = evars''; subst_metam = metas0 } =
            unify_0 ~metas:metas0 curenv evd CONV flags rhs v in
          w_merge_rec metas0 evd (metas'@metas) (evars''@evars') eqns
        else begin
          (* This can make rhs' ill-typed if metas are *)
          let rhs' = subst_meta_instances evd metas rhs in
          match EConstr.kind evd rhs with
          | App (f,cl) when occur_meta evd rhs' ->
              if occur_evar evd evk rhs' then
                error_occur_check curenv evd evk rhs';
              if is_mimick_head evd flags.modulo_delta f then
                let metas0, evd' = mimick_undefined_evar metas0 evd flags f cl evk in
                w_merge_rec metas0 evd' metas evars eqns
              else
                let metas0, evd' =
                  let env' = pop_rel_context nb curenv in
                  let evd', metas0, rhs'' = pose_all_metas_as_evars ~metas:metas0 env' evd rhs' in
                  try metas0, solve_simple_evar_eqn eflags curenv evd' ev rhs''
                    with Retyping.RetypeError _ ->
                      error_cannot_unify curenv evd' (mkEvar ev,rhs'')
                in
                w_merge_rec metas0 evd' metas evars' eqns
          | _ ->
              let evd', metas0, rhs'' = pose_all_metas_as_evars ~metas:metas0 env evd rhs' in
              let evd' =
                try solve_simple_evar_eqn eflags curenv evd' ev rhs''
                with Retyping.RetypeError _ -> error_cannot_unify curenv evd' (mkEvar ev, rhs'')
              in
              w_merge_rec metas0 evd' metas evars' eqns
        end
    | [] ->

    (* Process metas *)
    match metas with
    | (mv,c,(status,to_type))::metas ->
        let ((evd,metas0,c),(metas'',evars'')),eqns =
          if with_types && to_type != TypeProcessed then
            begin match to_type with
            | CoerceToType ->
              (* Some coercion may have to be inserted *)
              (w_coerce ~metas:metas0 env evd mv c,([],[])),eqns
            | _ ->
              (* No coercion needed: delay the unification of types *)
              ((evd,metas0,c),([],[])),(mv,status,c)::eqns
            end
          else
            ((evd,metas0,c),([],[])),eqns
        in
        begin match Meta.meta_opt_fvalue0 metas0 mv with
        | Some ({ rebus = c' }, (status', _)) ->
            let (take_left, st, { subst_sigma = evd; subst_metas = metas'; subst_evars = evars'; subst_metam = metas0 }) =
              merge_instances ~metas:metas0 env evd flags status' status c' c
            in
            let metas0 =
              if take_left then metas0
              else Meta.meta_reassign mv (c,(st,TypeProcessed)) metas0
            in
            w_merge_rec metas0 evd (metas'@metas@metas'') (evars'@evars'') eqns
        | None ->
            let evd', metas0 =
              if occur_meta_evd ~metas:metas0 evd mv c then
                let metas = Meta.meta_handler metas0 in
                if isMetaOf evd mv (whd_all ~metas env evd c) then evd, metas0
                else error_cannot_unify env evd (mkMeta mv,c)
              else
                Meta.meta_assign0 mv (c,(status,TypeProcessed)) metas0 evd
            in
            w_merge_rec metas0 evd' (metas''@metas) evars'' eqns
        end
    | [] ->
        (* Process type eqns *)
        let rec process_eqns failures = function
          | (mv,status,c)::eqns ->
              (match (try Inl (unify_type ~metas:metas0 env evd flags mv status c)
                      with e when CErrors.noncritical e -> Inr e)
               with
               | Inr e -> process_eqns (((mv,status,c),e)::failures) eqns
               | Inl { subst_sigma = evd; subst_metas = metas; subst_evars = evars; subst_metam = metas0 } ->
                   w_merge_rec metas0 evd metas evars (List.map fst failures @ eqns))
          | [] ->
              (match failures with
               | [] -> metas0, evd
               | ((mv,status,c),e)::_ -> raise e)
        in process_eqns [] eqns

  and mimick_undefined_evar metas0 evd flags hdc args sp =
    let ev = Evd.find_undefined evd sp in
    let sp_env = reset_with_named_context (evar_filtered_hyps ev) env in
    let (evd', c) = applyHead ~metas:metas0 sp_env evd hdc args in
    let { subst_sigma = evd''; subst_metas = mc; subst_evars = ec; subst_metam = metas0 } =
      unify_0 ~metas:metas0 sp_env evd' CUMUL flags
        (get_type_of sp_env evd' c) (Evd.evar_concl ev) in
    let metas0, evd''' = w_merge_rec metas0 evd'' mc ec [] in
    if evd' == evd''' (* FIXME ? *)
    then metas0, Evd.define sp c evd'''
    else metas0, Evd.define sp (Evarutil.nf_evar evd''' c) evd'''

  in

  let check_types ~metas evd =
    let eqns = Metamap.fold (fun mv b acc ->
      match b with
      | Clval (n, (t, (c, TypeNotProcessed)), v) -> (mv, c, t.rebus) :: acc
      | _ -> acc) metas []
    in w_merge_rec metas evd [] [] (List.rev eqns)
  in
  let { subst_sigma = evd; subst_metas = metas; subst_evars = evars; subst_metam = metas0 } = substn in
  let metas0, res =  (* merge constraints *)
    w_merge_rec metas0 evd (order_metas metas)
                (* Assign evars in the order of assignments during unification *)
                (List.rev evars) []
  in
  if with_types then check_types ~metas:metas0 res else metas0, res

let w_unify_meta_types ~metas env ?(flags=default_unify_flags ()) evd =
  let metas, metas0 = Meta.retract_coercible_metas metas in
  w_merge env true flags.merge_unify_flags { subst_sigma = evd; subst_metas = metas; subst_evars = []; subst_metam = metas0 }

(* [w_unify env evd M N]
   performs a unification of M and N, generating a bunch of
   unification constraints in the process.  These constraints
   are processed, one-by-one - they may either generate new
   bindings, or, if there is already a binding, new unifications,
   which themselves generate new constraints.  This continues
   until we get failure, or we run out of constraints.
   [clenv_typed_unify M N clenv] expects in addition that expected
   types of metavars are unifiable with the types of their instances    *)

let head_app ~metas env sigma m =
  let metas = Meta.meta_handler metas in
  fst (whd_nored_state ~metas env sigma (m, Stack.empty))

let isEvar_or_Meta sigma c = match EConstr.kind sigma c with
| Evar _ | Meta _ -> true
| _ -> false

let check_types env flags subst m n =
  let sigma = subst.subst_sigma in
  let metas = subst.subst_metam in
  if isEvar_or_Meta sigma (head_app ~metas env sigma m) then
    unify_0_with_initial_metas subst true env CUMUL
      flags
      (get_type_of_with_metas ~metas env sigma n, Unknown)
      (get_type_of_with_metas ~metas env sigma m, Unknown)
  else if isEvar_or_Meta sigma (head_app ~metas env sigma n) then
    unify_0_with_initial_metas subst true env CUMUL
      flags
      (get_type_of_with_metas ~metas env sigma m, Unknown)
      (get_type_of_with_metas ~metas env sigma n, Unknown)
  else subst

let try_resolve_typeclasses env evd flag m n =
  if flag then
    Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env evd
  else evd

let w_unify_core_0 ~metas env evd with_types cv_pb flags m n =
  let (mc1, metas0) = Meta.retract_coercible_metas metas in
  let substn = check_types env (set_flags_for_type flags.core_unify_flags) { subst_sigma = evd; subst_metas = mc1; subst_evars = []; subst_metam = metas0 } (fst m) (fst n) in
  let subst2 =
     unify_0_with_initial_metas substn false env cv_pb
       flags.core_unify_flags m n
  in
  let metas, evd = w_merge env with_types flags.merge_unify_flags subst2 in
  metas, try_resolve_typeclasses env evd flags.resolve_evars m n

let w_typed_unify ~metas env evd = w_unify_core_0 ~metas env evd true

let w_typed_unify_array ~metas env evd flags f1 l1 f2 l2 =
  let f1,l1,f2,l2 = adjust_app_array_size f1 l1 f2 l2 in
  let (mc1, metas0) = Meta.retract_coercible_metas metas in
  let fold_subst subst m n = unify_0_with_initial_metas subst true env CONV flags.core_unify_flags (m, Unknown) (n, Unknown) in
  let subst = fold_subst { subst_sigma = evd; subst_metas = []; subst_evars = []; subst_metam = metas0 } f1 f2 in
  let subst = Array.fold_left2 fold_subst subst l1 l2 in
  let metas, evd = w_merge env true flags.merge_unify_flags subst in
  metas, try_resolve_typeclasses env evd flags.resolve_evars
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

let default_matching_core_flags sigma =
  let ts = TransparentState.full in {
  modulo_conv_on_closed_terms = Some TransparentState.empty;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = TransparentState.empty;
  modulo_delta_types = ts;
  check_applied_meta_types = true;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = false;
  allowed_evars = allow_new_evars sigma;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = false;
}

let default_matching_merge_flags sigma =
  let ts = TransparentState.full in
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
      let flags = default_matching_flags (Option.default Evd.empty pending) in
      { flags with core_unify_flags = { flags.core_unify_flags with
        modulo_conv_on_closed_terms = Some TransparentState.full;
        restrict_conv_on_strict_subterms = true } }
    else default_matching_flags (Option.default Evd.empty pending) in
  let n = Array.length (snd (decompose_app sigma c)) in
  let cgnd = if occur_meta_or_undefined_evar sigma c then NotGround else Ground in
  let exception NotUnifiable in
  let matching_fun k _ t =
    (* make_pattern_test is only ever called with an empty rel context *)
    if 0 < k && not (EConstr.Vars.closed0 sigma t) then Result.Error ()
    else try
      let t',l2 =
        if from_prefix_of_ind then
          (* We check for fully applied subterms of the form "u u1 .. un" *)
          (* of inductive type knowing only a prefix "u u1 .. ui" *)
          let t,l = decompose_app_list sigma t in
          let l1,l2 =
            try List.chop n l with Failure _ -> raise NotUnifiable in
          if not (List.for_all (fun c -> Vars.closed0 sigma c) l2) then raise NotUnifiable
          else applist (t,l1), l2
        else t, [] in
      let metas = Metamap.empty in (* FIXME ? *)
      let _metas, sigma = w_typed_unify ~metas env sigma Conversion.CONV flags (c, cgnd) (t', Unknown) in
      let ty = Retyping.get_type_of env sigma t in
      if is_correct_type ty then Result.Ok (sigma, t, l2)
      else Result.Error ()
    with
    | PretypeError (_,_,CannotUnify (c1,c2,Some e)) ->
      Result.Error ()
    | NotUnifiable -> Result.Error ()
    (* MS: This is pretty bad, it catches Not_found for example *)
    | e when CErrors.noncritical e -> Result.Error ()
  in
  let merge_fun c1 c2 = match c2 with
  | Some (evd, c2, _) ->
    let (_, c1, x) = c1 in
    begin match infer_conv ~pb:CONV env evd c1 c2 with
    | Some evd ->
      let t1 = get_type_of env evd c1 in
      let t2 = get_type_of env evd c2 in
      begin match infer_conv ~pb:CONV env evd t1 t2 with
      | Some evd -> Result.Ok (Some (evd, c1, x))
      | None -> Result.Error ()
      end
    | None -> Result.Error ()
    end
  | None -> Result.Ok (Some c1)
  in
  { match_fun = matching_fun; merge_fun = merge_fun;
    testing_state = None; last_found = None },
  (fun test -> match test.testing_state with
  | None -> None
  | Some (sigma,_,l) ->
    let metas = Metamap.empty in (* FIXME ? *)
    let rec strong_whd_meta t = EConstr.map sigma strong_whd_meta (whd_meta ~metas sigma t) in
    let c = applist (strong_whd_meta c, l) in
     Some (sigma, c))

let make_eq_test env evd c =
  let out cstr =
    match cstr.last_found with None -> None | _ -> Some (cstr.testing_state, c)
  in
  (make_eq_univs_test env evd c, out)

let get_rigid_evars sigma c =
  let rec aux vars c = match EConstr.kind sigma c with
  | Var id -> Id.Set.add id vars
  | Evar _ -> vars (* do not take evar instances into account *)
  | _ -> EConstr.fold sigma aux vars c in
  aux Id.Set.empty c

let make_abstraction_core name (test,out) env sigma c ty occs check_occs concl =
  let id =
    let t = match ty with Some t -> t | None -> get_type_of env sigma c in
    let x = id_of_name_using_hdchar env sigma t name in
    let ids = Environ.ids_of_named_context_val (named_context_val env) in
    if name == Anonymous then next_ident_away_in_goal env x ids else
    if mem_named_context_val x (named_context_val env) then
      user_err
        (str "The variable " ++ Id.print x ++ str " is already declared.")
    else
      x
  in
  let likefirst = clause_with_generic_occurrences occs in
  let mkvarid () = EConstr.mkVar id in
  let compute_dependency _ d (remvars,sign,depdecls) =
    let d = EConstr.of_named_decl d in
    let hyp = NamedDecl.get_id d in
    if Id.Set.is_empty remvars then
    match occurrences_of_hyp hyp occs with
    | NoOccurrences, InHyp ->
        (remvars,push_named_context_val d sign,depdecls)
    | (AllOccurrences | AtLeastOneOccurrence), InHyp as occ ->
        let occ = if likefirst then LikeFirst else AtOccs occ in
        let newdecl = replace_term_occ_decl_modulo env sigma occ test mkvarid d in
        if Context.Named.Declaration.equal (ERelevance.equal sigma) (EConstr.eq_constr sigma) d newdecl
           && not (indirectly_dependent sigma c d depdecls)
        then
          if check_occs && not (in_every_hyp occs)
          then raise (PretypeError (env,sigma,NoOccurrenceFound (c,Some hyp)))
          else (remvars,push_named_context_val d sign, depdecls)
        else
          (remvars,push_named_context_val newdecl sign, newdecl :: depdecls)
    | occ ->
        (* There are specific occurrences, hence not like first *)
        let newdecl = replace_term_occ_decl_modulo env sigma (AtOccs occ) test mkvarid d in
        (remvars,push_named_context_val newdecl sign, newdecl :: depdecls)
    else
      (* Skip declarations if all rigid variables have not been introduced *)
      let remvars = Id.Set.remove hyp remvars in
      (remvars,push_named_context_val d sign,depdecls)
  in
  let vars = get_rigid_evars sigma c in
  try
    let _,sign,depdecls =
      fold_named_context compute_dependency env
        ~init:(vars,empty_named_context_val,[]) in
    let ccl = match occurrences_of_goal occs with
      | NoOccurrences -> concl
      | occ ->
          let occ = if likefirst then LikeFirst else AtOccs occ in
          replace_term_occ_modulo env sigma occ test mkvarid concl
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
| AbstractPattern of prefix_of_inductive_support_flag * (types -> bool) * Name.t * (evar_map option * constr) * clause
| AbstractExact of Name.t * constr * types option * clause * bool

type 'r abstraction_result =
  Names.Id.t * named_context_val *
    named_declaration list * Names.Id.t option *
    types * (evar_map * constr) option

let make_abstraction env evd ccl abs =
  match abs with
  | AbstractPattern (from_prefix,check,name,c,occs) ->
      make_abstraction_core name
        (make_pattern_test from_prefix check env evd c)
        env evd (snd c) None occs false ccl
  | AbstractExact (name,c,ty,occs,check_occs) ->
      make_abstraction_core name
        (make_eq_test env evd c)
        env evd c ty occs check_occs ccl

let keyed_unify env evd kop =
  if not (is_keyed_unification ()) then fun cl -> true
  else
    match kop with
    | None -> fun _ -> true
    | Some kop ->
      fun cl ->
        let kc = Keys.constr_key env (fun c -> EConstr.kind evd c) cl in
          match kc with
          | None -> false
          | Some kc -> Keys.equiv_keys kop kc

type 'aconstr akind =
  | AApp of 'aconstr * 'aconstr array
  | ACast of 'aconstr (* only the main term *)
  | AOther of 'aconstr array

module AConstr :
sig
  type t
  val proj : t -> EConstr.t
  val make : evar_map -> EConstr.t -> t
  val kind : t -> t akind
  val mkApp : t * t array -> t
  val closed0 : t -> bool
end =
struct

type t = {
  proj : EConstr.t;
  self : t akind;
  data : int;
}

let proj c = c.proj

let closed0 c = Int.equal c.data 0

let max (i : int) (j : int) = if i < j then j else i
let max_array f a = Array.fold_left (fun n v -> max (f v) n) 0 a
let lift (i : int) = if Int.equal i 0 then 0 else i - 1
let liftn k (i : int) = if i < k then 0 else i - k

let data v = v.data

let kind v = v.self

let mkApp (c, al) =
  if Array.is_empty al then c
  else match kind c with
  | AApp (c0, al0) ->
    { proj = mkApp (c.proj, Array.map proj al); self = AApp (c0, Array.append al0 al); data = max c.data (max_array data al) }
  | _ ->
    { proj = mkApp (c.proj, Array.map proj al); self = AApp (c, al); data = max c.data (max_array data al) }

let get_max_rel sigma c =
  let rec aux n accu c = match EConstr.kind sigma c with
  | Rel i -> if i <= n then accu else max accu (i - n)
  | _ -> EConstr.fold_with_binders sigma succ aux n accu c
  in
  aux 0 0 c

let get_max_rel_array sigma v = Array.fold_left (fun accu c -> max accu (get_max_rel sigma c)) 0 v

let anorec = AOther [||]

let rec make sigma c0 = match EConstr.kind sigma c0 with
| (Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ | String _) ->
  { proj = c0; self = anorec; data = 0 }
| Rel n ->
  { proj = c0; self = anorec; data = n }
| Cast (c, k, t) ->
  let c = make sigma c in
  (* unification doesn't recurse in the type *)
  let td = get_max_rel sigma t in
  { proj = c0; self = ACast c; data = max c.data td }
| Lambda (na, t, c) | Prod (na, t, c) ->
  let t = make sigma t in
  let c = make sigma c in
  { proj = c0; self = AOther [|t; c|]; data = max t.data (lift c.data) }
| LetIn (na, b, t, c) ->
  let b = make sigma b in
  (* unification doesn't recurse in the type *)
  let td = get_max_rel sigma t in
  let c = make sigma c in
  { proj = c0; self = AOther [|b; c|]; data = max b.data (max td (lift c.data)) }
| App (c, al) ->
  let c = make sigma c in
  let ald, al = make_array sigma al in
  { proj = c0; self = AApp (c, al); data = max c.data ald }
| Proj (p, _, t) ->
  let t = make sigma t in
  { proj = c0; self = AOther [|t|]; data = t.data }
| Evar (e, al) ->
  (* Unification doesn't recurse on the subterms in evar instances *)
  let data = SList.Skip.fold (fun accu v -> max accu (get_max_rel sigma v)) 0 al in
  { proj = c0; self = AOther [||]; data }
| Case (ci, u, pms, (p,_), iv, c, bl) ->
  let pmsd = get_max_rel_array sigma pms in
  let pd =
    let (nas, p) = p in
    let pd = get_max_rel sigma p in
    liftn (Array.length nas) pd
  in
  let ivd = match iv with
  | NoInvert -> 0
  | CaseInvert { indices } -> get_max_rel_array sigma indices
  in
  let c = make sigma c in
  let fold accu (nas, p) =
    let p = make sigma p in
    max accu (liftn (Array.length nas) p.data), p
  in
  let bld, bl = Array.fold_left_map fold 0 bl in
  let data = max pmsd @@ max pd @@ max ivd @@ max c.data bld in
  (* Unification only recurses on the discriminee and the branches *)
  { proj = c0; self = AOther (Array.append [|c|] bl); data }
| Fix (_, (_, tl, bl)) | CoFix(_,(_,tl,bl)) ->
  let tld, tl = make_array sigma tl in
  let bld, bl = make_array sigma bl in
  let data = max tld (liftn (Array.length tl) bld) in
  { proj = c0; self = AOther (Array.append tl bl); data }
| Array(u,t,def,ty) ->
  let td, t = make_array sigma t in
  let def = make sigma def in
  let ty = make sigma ty in
  let data = max td (max def.data ty.data) in
  { proj = c0; self = AOther (Array.append [|def;ty|] t); data }

and make_array sigma v =
  let fold accu c =
    let c = make sigma c in
    max accu c.data, c
  in
  Array.fold_left_map fold 0 v

end

(* Tries to find an instance of term [cl] in term [op].
   Unifies [cl] to every subterm of [op] until it finds a match.
   Fails if no match is found *)
let w_unify_to_subterm ~metas env evd ?(flags=default_unify_flags ()) (op,cl) =
  let bestexn = ref None in
  let kop = Keys.constr_key env (fun c -> EConstr.kind evd c) op in
  let opgnd = if occur_meta_or_undefined_evar evd op then NotGround else Ground in
  let rec matchrec cl =
    let rec strip_outer_cast c = match AConstr.kind c with
    | ACast c -> strip_outer_cast c
    | _ -> c
    in
    let cl = strip_outer_cast cl in
    (try
      let is_closed = AConstr.closed0 cl in
      let cl = AConstr.proj cl in
       if is_closed && not (isEvar evd cl) && keyed_unify env evd kop cl then
       (try
         if is_keyed_unification () then
           let f1, l1 = decompose_app evd op in
           let f2, l2 = decompose_app evd cl in
           w_typed_unify_array ~metas env evd flags f1 l1 f2 l2,cl
         else w_typed_unify ~metas env evd CONV flags (op, opgnd) (cl, Unknown),cl
       with ex when Pretype_errors.unsatisfiable_exception ex ->
            bestexn := Some ex; user_err Pp.(str "Unsat"))
       else user_err Pp.(str "Bound 1")
     with ex when precatchable_exception ex ->
       (match AConstr.kind cl with
        | ACast _ -> assert false (* just got stripped *)
        | AApp (f,args) ->
          let n = Array.length args in
          assert (n>0);
          let c1 = AConstr.mkApp (f,Array.sub args 0 (n-1)) in
          let c2 = args.(n-1) in
          (try
             matchrec c1
           with ex when precatchable_exception ex ->
             matchrec c2)
        | AOther a -> iter_fail matchrec a))
  in
  try matchrec cl
  with ex when precatchable_exception ex ->
    match !bestexn with
    | None -> raise (PretypeError (env,evd,NoOccurrenceFound (op, None)))
    | Some e -> raise e

(* Tries to find all instances of term [cl] in term [op].
   Unifies [cl] to every subterm of [op] and return all the matches.
   Fails if no match is found *)
let w_unify_to_subterm_all ~metas env evd ?(flags=default_unify_flags ()) (op,cl) =
  let return a b =
    let ((metas, evd), c as a) = a () in
      if List.exists (fun ((metas', evd'), c') -> EConstr.eq_constr evd' c c') b then b else a :: b
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
  let opgnd = if occur_meta_or_undefined_evar evd op then NotGround else Ground in
  let rec matchrec cl =
    let cl = strip_outer_cast evd cl in
      (bind
          (if closed0 evd cl
          then return (fun () -> w_typed_unify ~metas env evd CONV flags (op, opgnd) (cl, Unknown),cl)
            else fail "Bound 1")
          (match EConstr.kind evd cl with
            | App (f,args) ->
                let n = Array.length args in
                assert (n>0);
                let c1 = mkApp (f,Array.sub args 0 (n-1)) in
                let c2 = args.(n-1) in
                bind (matchrec c1) (matchrec c2)

            | Case(_,_,_,_,_,c,lf) -> (* does not search in the predicate *)
                bind (matchrec c) (bind_iter matchrec (Array.map snd lf))

            | Proj (p,_,c) -> matchrec c

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

            | Array(_u,t,def,ty) ->
              bind (bind (bind_iter matchrec t) (matchrec def)) (matchrec ty)

          | Cast (_, _, _)  -> fail "Match_subterm" (* Is this expected? *)

          | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Const _ | Ind _
            | Construct _ | Int _ | Float _ | String _ -> fail "Match_subterm"))

  in
  let res = matchrec cl [] in
  match res with
  | [] ->
    raise (PretypeError (env,evd,NoOccurrenceFound (op, None)))
  | _ ->
    List.map fst res

let w_unify_to_subterm_list ~metas env evd flags hdmeta oplist t =
  List.fold_right
    (fun op (metas,evd,l) ->
      let op = whd_meta ~metas evd op in
      if isMeta evd op then
        if flags.allow_K_in_toplevel_higher_order_unification then (metas,evd,op::l)
        else
          let hdname = Meta.meta_name metas hdmeta in
          let argname = Meta.meta_name metas (destMeta evd op) in
          error_abstraction_over_meta env evd hdname argname
      else
        let allow_K = flags.allow_K_in_toplevel_higher_order_unification in
        let flags =
          if is_keyed_unification () || occur_meta_or_existential evd op then
            (* This is up to delta for subterms w/o metas ... *)
            flags
          else
            (* up to Nov 2014, unification was bypassed on evar/meta-free terms;
               now it is called in a minimalistic way, at least to possibly
               unify pre-existing non frozen evars of the goal or of the
               pattern *)
          set_no_delta_flags flags in
        let t' = (strip_outer_cast evd op, AConstr.make evd t) in
        let ((metas', evd'), cl) =
          try
            if is_keyed_unification () then
              try (* First try finding a subterm w/o conversion on open terms *)
                let flags = set_no_delta_open_flags flags in
                w_unify_to_subterm ~metas env evd ~flags t'
              with e when CErrors.noncritical e ->
                (* If this fails, try with full conversion *)
                w_unify_to_subterm ~metas env evd ~flags t'
            else w_unify_to_subterm ~metas env evd ~flags t'
          with PretypeError (env,_,NoOccurrenceFound _) when
              allow_K ||
                (* w_unify_to_subterm does not go through evars, so
                   the next step, which was already in <= 8.4, is
                   needed at least for compatibility of rewrite *)
                dependent evd op t -> ((metas, evd), op)
        in
          if not allow_K &&
            (* ensure we found a different instance *)
            List.exists (fun op -> EConstr.eq_constr evd' op cl) l
          then
            let hdname = Meta.meta_name metas' hdmeta in
            error_non_linear_unification env evd hdname cl
          else (metas',evd',cl::l))
    oplist
    (metas,evd,[])

let w_unify_to_subterm env sigma ?flags (c, t) =
  w_unify_to_subterm env sigma ?flags (c, AConstr.make sigma t)

let secondOrderAbstraction ~metas env evd flags typ (p, oplist) =
  (* Remove delta when looking for a subterm *)
  let flags = { flags with core_unify_flags = flags.subterm_unify_flags } in
  let (metas,evd',cllist) = w_unify_to_subterm_list ~metas env evd flags p oplist typ in
  let typp = Meta.meta_type metas env evd' p in
  let evd',(pred,predtyp) = abstract_list_all env evd' typp typ cllist in
  match infer_conv ~pb:CUMUL env evd' predtyp typp with
  | None ->
    error_wrong_abstraction_type env evd'
      (Meta.meta_name metas p) pred typp predtyp;
  | Some evd' ->
  w_merge env false flags.merge_unify_flags
    { subst_sigma = evd'; subst_metas = [p,pred,(Conv,TypeProcessed)]; subst_evars = []; subst_metam = metas }

let secondOrderDependentAbstraction ~metas env evd flags typ (p, oplist) =
  let typp = Meta.meta_type metas env evd p in
  let evd, pred = abstract_list_all_with_dependencies env evd typp typ oplist in
  w_merge env false flags.merge_unify_flags
    { subst_sigma = evd; subst_metas = [p,pred,(Conv,TypeProcessed)]; subst_evars = []; subst_metam = metas }


let secondOrderAbstractionAlgo dep =
  if dep then secondOrderDependentAbstraction else secondOrderAbstraction

let w_unify2 ~metas env evd flags dep cv_pb ty1 ty2 =
  let c1, oplist1 = whd_nored_stack ~metas:(Meta.meta_handler metas) env evd ty1 in
  let c2, oplist2 = whd_nored_stack ~metas:(Meta.meta_handler metas) env evd ty2 in
  match EConstr.kind evd c1, EConstr.kind evd c2 with
    | Meta p1, _ ->
        (* Find the predicate *)
        secondOrderAbstractionAlgo dep ~metas env evd flags ty2 (p1, oplist1)
    | _, Meta p2 ->
        (* Find the predicate *)
        secondOrderAbstractionAlgo dep ~metas env evd flags ty1 (p2, oplist2)
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
let w_unify ~metas env evd cv_pb ?(flags=default_unify_flags ()) ty1 ty2 =
  let hd1,l1 = decompose_app evd (whd_nored ~metas:(Meta.meta_handler metas) env evd ty1) in
  let hd2,l2 = decompose_app evd (whd_nored ~metas:(Meta.meta_handler metas) env evd ty2) in
  let is_empty1 = Array.is_empty l1 in
  let is_empty2 = Array.is_empty l2 in
    match EConstr.kind evd hd1, not is_empty1, EConstr.kind evd hd2, not is_empty2 with
      (* Pattern case *)
      | (Meta _, true, Lambda _, _ | Lambda _, _, Meta _, true)
          when Int.equal (Array.length l1) (Array.length l2) ->
          (try
              w_typed_unify_array ~metas env evd flags hd1 l1 hd2 l2
            with ex when precatchable_exception ex ->
              try
                w_unify2 ~metas env evd flags false cv_pb ty1 ty2
              with PretypeError (env,_,NoOccurrenceFound _) as e -> raise e)

      (* Second order case *)
      | (Meta _, true, _, _ | _, _, Meta _, true) ->
          (try
              w_unify2 ~metas env evd flags false cv_pb ty1 ty2
            with PretypeError (env,_,NoOccurrenceFound _) as e -> raise e
              | ex when precatchable_exception ex ->
                  try
                    w_typed_unify_array ~metas env evd flags hd1 l1 hd2 l2
                  with ex' when precatchable_exception ex' ->
                    (* Last chance, use pattern-matching with typed
                       dependencies (done late for compatibility) *)
                    try
                      w_unify2 ~metas env evd flags true cv_pb ty1 ty2
                    with ex' when precatchable_exception ex' ->
                      raise ex)

      (* General case: try first order *)
      | _ -> w_typed_unify ~metas env evd cv_pb flags (ty1, Unknown) (ty2, Unknown)

let w_unify ?(metas = Metamap.empty) env evd cv_pb ?(flags=default_unify_flags ()) ty1 ty2 =
  w_unify ~metas env evd cv_pb ~flags ty1 ty2

let w_unify_to_subterm ?(metas = Metamap.empty) env evd ?flags arg =
  w_unify_to_subterm ~metas env evd ?flags arg

let w_unify_to_subterm_all ?(metas = Metamap.empty) env evd ?flags arg =
  w_unify_to_subterm_all ~metas env evd ?flags arg

let w_unify_meta_types ?(metas = Metamap.empty) env ?flags evd =
  w_unify_meta_types ~metas env ?flags evd

let w_coerce_to_type ?(metas = Metamap.empty) env evd c cty mvty =
  w_coerce_to_type ~metas env evd c cty mvty

let pose_all_metas_as_evars ~metas env evd ty =
  let metas, sigma, c = pose_all_metas_as_evars ~metas env evd ty in
  metas, sigma, c
