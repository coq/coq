(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file contains the syntax-directed part of the type inference
   algorithm introduced by Murthy in Coq V5.10, 1995; the type
   inference algorithm was initially developed in a file named trad.ml
   which formerly contained a simple concrete-to-abstract syntax
   translation function introduced in CoC V4.10 for implementing the
   "exact" tactic, 1989 *)
(* Support for typing term in Ltac environment by David Delahaye, 2000 *)
(* Type inference algorithm made a functor of the coercion and
   pattern-matching compilation by Matthieu Sozeau, March 2006 *)
(* Fixpoint guard index computation by Pierre Letouzey, July 2007 *)

(* Structural maintainer: Hugo Herbelin *)
(* Secondary maintenance: collective *)


open Pp
open CErrors
open Util
open Names
open Evd
open Constr
open Context
open Termops
open Environ
open EConstr
open Vars
open Reductionops
open Type_errors
open Typing
open Evarutil
open Evardefine
open Pretype_errors
open Glob_term
open Glob_ops
open GlobEnv
open Evarconv

module NamedDecl = Context.Named.Declaration

type typing_constraint = IsType | OfType of types | WithoutTypeConstraint

let (!!) env = GlobEnv.env env

let bidi_hints =
  Summary.ref (GlobRef.Map.empty : int GlobRef.Map.t) ~name:"bidirectionalityhints"

let add_bidirectionality_hint gr n =
  bidi_hints := GlobRef.Map.add gr n !bidi_hints

let get_bidirectionality_hint gr =
  GlobRef.Map.find_opt gr !bidi_hints

let clear_bidirectionality_hint gr =
  bidi_hints := GlobRef.Map.remove gr !bidi_hints

(************************************************************************)
(* This concerns Cases *)
open Inductive
open Inductiveops

(************************************************************************)

(* An auxiliary function for searching for fixpoint guard indices *)

(* Tells the possible indices liable to guard a fixpoint *)
type possible_fix_indices = int list list

(* Tells if possibly a cofixpoint or a fixpoint over the given list of possible indices *)
type possible_guard = {
  possibly_cofix : bool;
  possible_fix_indices : possible_fix_indices;
} (* Note: if no fix indices are given, it has to be a cofix *)

exception Found of int array option

let nf_fix sigma (nas, cs, ts) =
  let inj c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  (Array.map EConstr.Unsafe.to_binder_annot nas, Array.map inj cs, Array.map inj ts)

let search_guard ?loc ?evars env {possibly_cofix; possible_fix_indices} fixdefs =
  let is_singleton = function [_] -> true | _ -> false in
  let one_fix_possibility = List.for_all is_singleton possible_fix_indices in
  if one_fix_possibility && not possibly_cofix then
    let indexes = Array.of_list (List.map List.hd possible_fix_indices) in
    let fix = ((indexes, 0), fixdefs) in
    try let () = check_fix ?evars env fix in Some indexes
    with reraise ->
      let (e, info) = Exninfo.capture reraise in
      let info = Option.cata (fun loc -> Loc.add_loc info loc) info loc in
      Exninfo.iraise (e, info)
  else
    let zero_fix_possibility = List.for_all List.is_empty possible_fix_indices in
    if zero_fix_possibility && possibly_cofix then
      (* Maybe can we skip this check since it will be done in the kernel again *)
      let cofix = (0, fixdefs) in
      try let () = check_cofix ?evars env cofix in None
      with reraise ->
        let (e, info) = Exninfo.capture reraise in
        let info = Option.cata (fun loc -> Loc.add_loc info loc) info loc in
        Exninfo.iraise (e, info)
    else
    (* we now search recursively among all combinations *)
    let combinations = List.combinations possible_fix_indices in
    let flags = { (typing_flags env) with Declarations.check_guarded = true } in
    let env = Environ.set_typing_flags flags env in
    try
       let () = List.iter
         (fun l ->
            let indexes = Array.of_list l in
            let fix = ((indexes, 0),fixdefs) in
            (* spiwack: We search for a unspecified structural
               argument under the assumption that we need to check the
               guardedness condition (otherwise the first inductive argument
               will be chosen). A more robust solution may be to raise an
               error when totality is assumed but the strutural argument is
               not specified. *)
            try
              let () = check_fix ?evars env fix in raise (Found (Some indexes))
            with TypeError _ -> ())
          combinations in
       let () =
         if possibly_cofix then
           (* Maybe can we skip this check since it will be done in the kernel again *)
           try let () = check_cofix env (0, fixdefs) in raise (Found None)
           with TypeError _ -> () in
       let errmsg = "Cannot guess decreasing argument of fix." in
       user_err ?loc (Pp.str errmsg)
     with Found indexes -> indexes

let search_fix_guard ?loc ?evars env possible_fix_indices fixdefs =
  Option.get (search_guard ?loc ?evars env {possibly_cofix=false; possible_fix_indices} fixdefs)

let esearch_guard ?loc env sigma indexes fix =
  (* not sure if we still need to nf_fix when calling search_guard with ~evars
     (here and other callers through the code)
     OTOH search_guard needs to go through the whole term to see possible recursive calls
     so we may as well upfront normalize *)
  let fix = nf_fix sigma fix in
  let evars = Evd.evar_handler sigma in
  try search_guard ?loc ~evars env indexes fix
  with TypeError (env,err) ->
    Loc.raise ?loc (PretypeError (env,sigma,TypingError (of_type_error err)))

let esearch_fix_guard ?loc env sigma possible_fix_indices fix =
  Option.get (esearch_guard ?loc env sigma {possibly_cofix=false; possible_fix_indices} fix)

let esearch_cofix_guard ?loc env sigma cofix =
  let res = esearch_guard ?loc env sigma {possibly_cofix=true; possible_fix_indices=[]} cofix in
  assert (Option.is_empty res)

(* To force universe name declaration before use *)

let { Goptions.get = is_strict_universe_declarations } =
  Goptions.declare_bool_option_and_ref
    ~key:["Strict";"Universe";"Declaration"]
    ~value:true
    ()

(** Miscellaneous interpretation functions *)

let universe_level_name evd ({CAst.v=id} as lid) =
  try evd, Evd.universe_of_name evd id
  with Not_found ->
    if not (is_strict_universe_declarations ()) then
      new_univ_level_variable ?loc:lid.CAst.loc ~name:id univ_rigid evd
    else user_err ?loc:lid.CAst.loc
        (Pp.(str "Undeclared universe: " ++ Id.print id ++ str "."))

let level_name sigma = function
  | GSProp | GProp -> None
  | GSet -> Some (sigma, Univ.Level.set)
  | GUniv u -> Some (sigma, u)
  | GRawUniv u ->
    let sigma = try Evd.add_forgotten_univ sigma u with UGraph.AlreadyDeclared -> sigma in
    Some (sigma, u)
  | GLocalUniv l ->
    let sigma, u = universe_level_name sigma l in
    Some (sigma, u)

let glob_level ?loc evd : glob_level -> _ = function
  | UAnonymous {rigid} ->
    assert (rigid <> UnivFlexible true);
    new_univ_level_variable ?loc rigid evd
  | UNamed s ->
    match level_name evd s with
    | None ->
      user_err ?loc
        (str "Universe instances cannot contain non-Set small levels," ++ spc() ++
         str "polymorphic universe instances must be greater or equal to Set.");
    | Some r -> r

let glob_qvar ?loc evd : glob_qvar -> _ = function
  | GQVar q -> evd, q
  | GLocalQVar {v=Anonymous} ->
    let evd, q = new_quality_variable ?loc evd in
    evd, q
  | GRawQVar q ->
    let evd = Evd.merge_sort_variables ~sideff:true evd (Sorts.QVar.Set.singleton q) in
    evd, q
  | GLocalQVar {v=Name id; loc} ->
    try evd, (Evd.quality_of_name evd id)
    with Not_found ->
      if not (is_strict_universe_declarations()) then
        let evd, q = new_quality_variable ?loc evd in
        evd, q
      else user_err ?loc Pp.(str "Undeclared quality: " ++ Id.print id ++ str".")

let glob_quality ?loc evd = let open Sorts.Quality in function
  | GQConstant q -> evd, QConstant q
  | GQualVar (GQVar _ | GLocalQVar _ | GRawQVar _ as q) ->
    let evd, q = glob_qvar ?loc evd q in
    evd, QVar q

type inference_hook = env -> evar_map -> Evar.t -> (evar_map * constr) option

type use_typeclasses = NoUseTC | UseTCForConv | UseTC

type inference_flags = {
  use_coercions : bool;
  use_typeclasses : use_typeclasses;
  solve_unification_constraints : bool;
  fail_evar : bool;
  expand_evars : bool;
  program_mode : bool;
  polymorphic : bool;
  undeclared_evars_patvars: bool;
  patvars_abstract : bool;
  unconstrained_sorts : bool;
}

type pretype_flags = {
  poly : bool;
  resolve_tc : bool;
  program_mode : bool;
  use_coercions : bool;
  undeclared_evars_patvars : bool;
  patvars_abstract : bool;
  unconstrained_sorts : bool;
}

let glob_opt_qvar ?loc ~flags sigma = function
  | None ->
    if flags.unconstrained_sorts then
      let sigma, q = new_quality_variable ?loc sigma in
      sigma, Some q
    else sigma, None
  | Some q ->
    let sigma, q = glob_qvar ?loc sigma q in
    sigma, Some q

let sort ?loc ~flags sigma (q, l) = match l with
| UNamed [] -> assert false
| UNamed [GSProp, 0] -> assert (Option.is_empty q); sigma, ESorts.sprop
| UNamed [GProp, 0] -> assert (Option.is_empty q); sigma, ESorts.prop
| UNamed [GSet, 0] when Option.is_empty q -> sigma, ESorts.set
| UNamed ((u, n) :: us) ->
  let open Pp in
  let sigma, q = glob_opt_qvar ?loc ~flags sigma q in
  let get_level sigma u n = match level_name sigma u with
  | None ->
    user_err ?loc
      (str "Non-Set small universes cannot be used in algebraic expressions.")
  | Some (sigma, u) ->
    let u = Univ.Universe.make u in
    let u = match n with
    | 0 -> u
    | 1 -> Univ.Universe.super u
    | n ->
      user_err ?loc
        (str "Cannot interpret universe increment +" ++ int n ++ str ".")
    in
    (sigma, u)
  in
  let fold (sigma, u) (l, n) =
    let sigma, u' = get_level sigma l n in
    (sigma, Univ.Universe.sup u u')
  in
  let (sigma, u) = get_level sigma u n in
  let (sigma, u) = List.fold_left fold (sigma, u) us in
  let s = match q with
    | None -> Sorts.sort_of_univ u
    | Some q -> Sorts.qsort q u
  in
  sigma, ESorts.make s
| UAnonymous {rigid} ->
  let sigma, q = glob_opt_qvar ?loc ~flags sigma q in
  let sigma, l = new_univ_level_variable ?loc rigid sigma in
  let u = Univ.Universe.make l in
  let s = match q with
    | None -> Sorts.sort_of_univ u
    | Some q -> Sorts.qsort q u
  in
  sigma, ESorts.make s

(* Compute the set of still-undefined initial evars up to restriction
   (e.g. clearing) and the set of yet-unsolved evars freshly created
   in the extension [sigma'] of [sigma] (excluding the restrictions of
   the undefined evars of [sigma] to be freshly created evars of
   [sigma']). Otherwise said, we partition the undefined evars of
   [sigma'] into those already in [sigma] or deriving from an evar in
   [sigma] by restriction, and the evars properly created in [sigma'] *)

type frozen_and_pending =
  Frz :
    'a Evar.Map.t
    (* Undefined from [sigma']. This is used only as a set,
       guaranteed by the existential type 'a, but we do not use
       Evar.Set to avoid reallocating. *)
    * Evar.Set.t Lazy.t option
    (* Undefined evars in [sigma'] which are neither in [sigma] or aliases thereof.
       [None] means empty.*)
    -> frozen_and_pending

let frozen_and_pending_holes (sigma, sigma') term =
  let undefined0 = Option.cata Evd.undefined_map Evar.Map.empty sigma in
  let included = Option.cata (Evd.evars_of_term sigma') Evar.Set.empty term in
  let pending =
    if undefined0 == Evd.undefined_map sigma' && Evar.Set.is_empty included
    then None
    else
      Some (lazy begin
        let pending, aliases =
          Evar.Map.symmetric_diff_fold (fun ev v v' (pending,aliases as acc) -> match v, v' with
              | None, None -> assert false
              | Some _, None ->
                (* ev got defined in sigma', but is it an alias? *)
                begin match advance sigma' ev with
                | None -> acc
                | Some ev -> pending, Evar.Set.add ev aliases
                end
              | None, Some _ ->
                (* ev is new in sigma' *)
                Evar.Set.add ev pending, aliases
              | Some _, Some _ -> (* ev is still undefined in sigma' *) acc)
            undefined0
            (Evd.undefined_map sigma')
            (Evar.Set.empty, Evar.Set.empty)
        in
        Evar.Set.union included (Evar.Set.diff pending aliases);
      end)
  in
  Frz (Evd.undefined_map sigma', pending)

let filter_frozen frozen = match frozen with
  | Frz (undf, None) -> fun evk -> Evar.Map.mem evk undf
  | Frz (undf, Some (lazy pending)) -> fun evk -> not (Evar.Set.mem evk pending) && Evar.Map.mem evk undf

let typeclasses_filter ~program_mode frozen =
  if program_mode
  then (fun evk evi -> Typeclasses.no_goals_or_obligations evk evi && not (filter_frozen frozen evk))
  else (fun evk evi -> Typeclasses.no_goals evk evi && not (filter_frozen frozen evk))

let apply_typeclasses ~program_mode ~fail_evar env sigma frozen =
  let sigma = Typeclasses.resolve_typeclasses
      ~filter:(typeclasses_filter ~program_mode frozen)
      ~fail:fail_evar env sigma in
  let sigma = if program_mode then (* Try optionally solving the obligations *)
      Typeclasses.resolve_typeclasses
        ~filter:(fun evk evi -> Typeclasses.all_evars evk evi && not (filter_frozen frozen evk)) ~fail:false env sigma
    else sigma in
  sigma

let apply_inference_hook (hook : inference_hook) env sigma frozen = match frozen with
| Frz (_, None) -> sigma
| Frz (_, Some (lazy pending)) ->
  Evar.Set.fold (fun evk sigma ->
    if Evd.is_undefined sigma evk (* in particular not defined by side-effect *)
    then
      match hook env sigma evk with
      | Some (sigma, c) ->
        Evd.define evk c sigma
      | None -> sigma
    else
      sigma) pending sigma

let allow_all_but_patvars sigma =
  let p evk =
    try
      let EvarInfo evi = Evd.find sigma evk in
      match snd (Evd.evar_source evi) with Evar_kinds.MatchingVar _ -> false | _ -> true
    with Not_found -> true
  in
  Evarsolve.AllowedEvars.from_pred p

let apply_heuristics ~patvars_abstract env sigma =
  (* Resolve eagerly, potentially making wrong choices *)
  let flags = default_flags_of (Conv_oracle.get_transp_state (Environ.oracle env)) in
  let flags = if patvars_abstract then { flags with allowed_evars = allow_all_but_patvars sigma } else flags in
  try solve_unif_constraints_with_heuristics ~flags env sigma
  with e when CErrors.noncritical e -> sigma

let check_typeclasses_instances_are_solved ~program_mode env sigma frozen =
  let tcs = Typeclasses.get_filtered_typeclass_evars
      (typeclasses_filter ~program_mode frozen)
      sigma
  in
  if not (Evar.Set.is_empty tcs) then begin
    Typeclasses.error_unresolvable env sigma tcs
  end

let check_extra_evars_are_solved env current_sigma frozen = match frozen with
| Frz (_, None) -> ()
| Frz (_, Some (lazy pending)) ->
  Evar.Set.iter
    (fun evk ->
      if not (Evd.is_defined current_sigma evk) then
        let (loc,k) = evar_source (Evd.find_undefined current_sigma evk) in
        match k with
        | Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
        | _ ->
            error_unsolvable_implicit ?loc env current_sigma evk None) pending

(* [check_evars] fails if some unresolved evar remains *)

let check_evars env ?initial sigma c =
  let rec proc_rec c =
    match EConstr.kind sigma c with
    | Evar (evk, _) ->
      (match initial with
       | Some initial when Evd.mem initial evk -> ()
       | _ ->
        let EvarInfo evi = Evd.find sigma evk in
         let (loc,k) = evar_source evi in
         begin match k with
           | Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
           | _ -> Pretype_errors.error_unsolvable_implicit ?loc env sigma evk None
         end)
    | _ -> EConstr.iter sigma proc_rec c
  in proc_rec c

let check_problems_are_solved env sigma = function
  | Frz (_, None) -> ()
  | Frz (_, Some (lazy pending)) -> check_problems_are_solved ~evars:pending env sigma

let check_evars_are_solved_from ~program_mode env sigma frozen frozen_for_pb =
  check_typeclasses_instances_are_solved ~program_mode env sigma frozen;
  check_problems_are_solved env sigma frozen_for_pb;
  check_extra_evars_are_solved env sigma frozen

(* Try typeclasses, hooks, unification heuristics ... *)

let solve_remaining_evars_from ?hook (flags : inference_flags) env ?initial sigma term =
  let program_mode = flags.program_mode in
  let sigma =
    match flags.use_typeclasses with
    | UseTC ->
      let frozen = frozen_and_pending_holes (initial, sigma) None in
      apply_typeclasses ~program_mode ~fail_evar:false env sigma frozen
    | NoUseTC | UseTCForConv -> sigma
  in
  let sigma = match hook with
  | None -> sigma
  | Some hook ->
    let frozen = frozen_and_pending_holes (initial, sigma) None in
    apply_inference_hook hook env sigma frozen
  in
  let sigma = if flags.solve_unification_constraints
    then apply_heuristics ~patvars_abstract:flags.patvars_abstract env sigma
    else sigma
  in
  let () = if flags.fail_evar then
    let frozen = frozen_and_pending_holes (initial, sigma) None in
    let frozen_for_pb = frozen_and_pending_holes (initial, sigma) term in
    check_evars_are_solved_from ~program_mode env sigma frozen frozen_for_pb in
  sigma

let solve_remaining_evars ?hook (flags : inference_flags) env ?initial sigma =
  solve_remaining_evars_from ?hook (flags : inference_flags) env ?initial sigma None

let check_evars_are_solved ~program_mode env ?initial current_sigma =
  let frozen = frozen_and_pending_holes (initial, current_sigma) None in
  check_evars_are_solved_from ~program_mode env current_sigma frozen frozen

let process_inference_flags flags env initial (sigma,c,cty) =
  let sigma = solve_remaining_evars_from flags env ~initial sigma (Some cty) in
  let c = if flags.expand_evars then nf_evar sigma c else c in
  sigma,c,cty

let adjust_evar_source sigma na c =
  match na, kind sigma c with
  | Name id, Evar (evk,args) ->
     let evi = Evd.find_undefined sigma evk in
     begin match Evd.evar_source evi with
     | loc, Evar_kinds.QuestionMark ({ Evar_kinds.qm_name=Anonymous } as qm) ->
       let src = (loc,Evar_kinds.QuestionMark { qm with Evar_kinds.qm_name=na }) in
       (* Evd.update_source doesn't work for some reason, cf test bug_18260_1.v *)
       let (sigma, evk') = Evd.restrict evk (evar_filter evi) ~src sigma in
       sigma, mkEvar (evk',args)
     | _ -> sigma, c
     end
  | _, _ -> sigma, c

(* coerce to tycon if any *)
let inh_conv_coerce_to_tycon ?loc ~flags:{ program_mode; resolve_tc; use_coercions; patvars_abstract } env sigma j = function
  | None -> sigma, j, Some Coercion.empty_coercion_trace
  | Some t ->
    Coercion.inh_conv_coerce_to ?loc ~program_mode ~resolve_tc ~use_coercions ~patvars_abstract !!env sigma j t

let check_instance subst = function
  | [] -> ()
  | (CAst.{loc;v=id},_) :: _ ->
      if List.mem_assoc id subst then
        user_err ?loc  (Id.print id ++ str "appears more than once.")
      else
        user_err ?loc  (str "No such variable in the signature of the existential variable: " ++ Id.print id ++ str ".")

(* used to enforce a name in Lambda when the type constraints itself
   is named, hence possibly dependent *)

let orelse_name name name' = match name with
  | Anonymous -> name'
  | _ -> name

let pretype_id pretype loc env sigma id =
  (* Look for the binder of [id] *)
  try
    let (n,_,typ) = lookup_rel_id id (rel_context !!env) in
    sigma, { uj_val  = mkRel n; uj_type = lift n typ }
  with Not_found ->
  try
    GlobEnv.interp_ltac_variable ?loc (fun env -> pretype env sigma) env sigma id
  with Not_found ->
  (* Check if [id] is a section or goal variable *)
  try
    sigma, { uj_val  = mkVar id; uj_type = NamedDecl.get_type (lookup_named id !!env) }
  with Not_found ->
    (* [id] not found, standard error message *)
    error_var_not_found ?loc !!env sigma id

(*************************************************************************)
(* Main pretyping function                                               *)

let instance ?loc evd (ql,ul) =
  let evd, ql' =
    List.fold_left
      (fun (evd, quals) l ->
         let evd, l = glob_quality ?loc evd l in
         (evd, l :: quals)) (evd, [])
      ql
  in
  let evd, ul' =
    List.fold_left
      (fun (evd, univs) l ->
         let evd, l = glob_level ?loc evd l in
         (evd, l :: univs)) (evd, [])
      ul
  in
  evd, Some (UVars.Instance.of_array (Array.rev_of_list ql', Array.rev_of_list ul'))

let pretype_global ?loc rigid env evd gr us =
  let evd, instance =
    match us with
    | None -> evd, None
    | Some l -> instance ?loc evd l
  in
  Evd.fresh_global ?loc ~rigid ?names:instance !!env evd gr

let pretype_ref ?loc sigma env ref us =
  match ref with
  | GlobRef.VarRef id ->
      (* Section variable *)
    (try
       let ty = NamedDecl.get_type (lookup_named id !!env) in
       (match us with
        | None | Some ([],[]) -> ()
        | Some (qs,us) ->
            let open UnivGen in
            Loc.raise ?loc (UniverseLengthMismatch {
              gref = ref;
              actual = List.length qs, List.length us;
              expect = 0, 0;
            }));
       sigma, make_judge (mkVar id) ty
       with Not_found ->
         (* This may happen if env is a goal env and section variables have
            been cleared - section variables should be different from goal
            variables *)
         Pretype_errors.error_var_not_found ?loc !!env sigma id)
  | ref ->
    let sigma, c = pretype_global ?loc univ_flexible env sigma ref us in
    let sigma, ty = type_of !!env sigma c in
    sigma, make_judge c ty

let judge_of_sort ?loc evd s =
  let judge =
    { uj_val = mkSort s; uj_type = mkSort (ESorts.super evd s) }
  in
    evd, judge

let pretype_sort ?loc ~flags sigma s =
  let sigma, s = sort ?loc ~flags sigma s in
  judge_of_sort ?loc sigma s

let new_typed_evar env sigma ?naming ~src tycon =
  match tycon with
  | Some ty ->
    let sigma, c = new_evar env sigma ~src ?naming ty in
    sigma, c, ty
  | None ->
    let sigma, ty = new_type_evar env sigma ~src in
    let sigma, c = new_evar env sigma ~src ?naming ty in
    let evk = fst (destEvar sigma c) in
    let ido = Evd.evar_ident evk sigma in
    let src = (fst src,Evar_kinds.EvarType (ido,evk)) in
    let sigma = update_source sigma (fst (destEvar sigma ty)) src in
    sigma, c, ty

let mark_obligation_evar sigma k evc =
  match k with
  | Evar_kinds.QuestionMark _
  | Evar_kinds.ImplicitArg (_, _, false) ->
    Evd.set_obligation_evar sigma (fst (destEvar sigma evc))
  | _ -> sigma

type 'a pretype_fun = ?loc:Loc.t -> flags:pretype_flags -> type_constraint -> GlobEnv.t -> evar_map -> evar_map * 'a

type pretyper = {
  pretype_ref : pretyper -> GlobRef.t * glob_instance option -> unsafe_judgment pretype_fun;
  pretype_var : pretyper -> Id.t -> unsafe_judgment pretype_fun;
  pretype_evar : pretyper -> existential_name CAst.t * (lident * glob_constr) list -> unsafe_judgment pretype_fun;
  pretype_patvar : pretyper -> Evar_kinds.matching_var_kind -> unsafe_judgment pretype_fun;
  pretype_app : pretyper -> glob_constr * glob_constr list -> unsafe_judgment pretype_fun;
  pretype_proj : pretyper -> (Constant.t * glob_instance option) * glob_constr list * glob_constr -> unsafe_judgment pretype_fun;
  pretype_lambda : pretyper -> Name.t * binding_kind * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_prod : pretyper -> Name.t * binding_kind * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_letin : pretyper -> Name.t * glob_constr * glob_constr option * glob_constr -> unsafe_judgment pretype_fun;
  pretype_cases : pretyper -> Constr.case_style * glob_constr option * tomatch_tuples * cases_clauses -> unsafe_judgment pretype_fun;
  pretype_lettuple : pretyper -> Name.t list * (Name.t * glob_constr option) * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_if : pretyper -> glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_rec : pretyper -> glob_fix_kind * Id.t array * glob_decl list array * glob_constr array * glob_constr array -> unsafe_judgment pretype_fun;
  pretype_sort : pretyper -> glob_sort -> unsafe_judgment pretype_fun;
  pretype_hole : pretyper -> Evar_kinds.glob_evar_kind -> unsafe_judgment pretype_fun;
  pretype_genarg : pretyper -> Genarg.glob_generic_argument -> unsafe_judgment pretype_fun;
  pretype_cast : pretyper -> glob_constr * cast_kind option * glob_constr -> unsafe_judgment pretype_fun;
  pretype_int : pretyper -> Uint63.t -> unsafe_judgment pretype_fun;
  pretype_float : pretyper -> Float64.t -> unsafe_judgment pretype_fun;
  pretype_string : pretyper -> Pstring.t -> unsafe_judgment pretype_fun;
  pretype_array : pretyper -> glob_instance option * glob_constr array * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_type : pretyper -> glob_constr -> unsafe_type_judgment pretype_fun;
}

(** Tie the loop *)
let eval_pretyper self ~flags tycon env sigma t =
  let loc = t.CAst.loc in
  match DAst.get t with
  | GRef (ref,u) ->
    self.pretype_ref self (ref, u) ?loc ~flags tycon env sigma
  | GVar id ->
    self.pretype_var self id ?loc ~flags tycon env sigma
  | GEvar (evk, args) ->
    self.pretype_evar self (evk, args) ?loc ~flags tycon env sigma
  | GPatVar knd ->
    self.pretype_patvar self knd ?loc ~flags tycon env sigma
  | GApp (c, args) ->
    self.pretype_app self (c, args) ?loc ~flags tycon env sigma
  | GProj (hd, args, c) ->
    self.pretype_proj self (hd, args, c) ?loc ~flags tycon env sigma
  | GLambda (na, _, bk, t, c) ->
    self.pretype_lambda self (na, bk, t, c) ?loc ~flags tycon env sigma
  | GProd (na, _, bk, t, c) ->
    self.pretype_prod self (na, bk, t, c) ?loc ~flags tycon env sigma
  | GLetIn (na, _, b, t, c) ->
    self.pretype_letin self (na, b, t, c) ?loc ~flags tycon env sigma
  | GCases (st, c, tm, cl) ->
    self.pretype_cases self (st, c, tm, cl) ?loc ~flags tycon env sigma
  | GLetTuple (na, b, t, c) ->
    self.pretype_lettuple self (na, b, t, c) ?loc ~flags tycon env sigma
  | GIf (c, r, t1, t2) ->
    self.pretype_if self (c, r, t1, t2) ?loc ~flags tycon env sigma
  | GRec (knd, nas, decl, c, t) ->
    self.pretype_rec self (knd, nas, decl, c, t) ?loc ~flags tycon env sigma
  | GSort s ->
    self.pretype_sort self s ?loc ~flags tycon env sigma
  | GHole knd ->
    self.pretype_hole self knd ?loc ~flags tycon env sigma
  | GGenarg arg ->
    self.pretype_genarg self arg ?loc ~flags tycon env sigma
  | GCast (c, k, t) ->
    self.pretype_cast self (c, k, t) ?loc ~flags tycon env sigma
  | GInt n ->
    self.pretype_int self n ?loc ~flags tycon env sigma
  | GFloat f ->
    self.pretype_float self f ?loc ~flags tycon env sigma
  | GString s ->
    self.pretype_string self s ?loc ~flags tycon env sigma
  | GArray (u,t,def,ty) ->
    self.pretype_array self (u,t,def,ty) ?loc ~flags tycon env sigma

let eval_type_pretyper self ~flags tycon env sigma t =
  self.pretype_type self t ~flags tycon env sigma

let pretype_instance self ~flags env sigma loc hyps evk update =
  let f decl (subst,update,sigma) =
    let id = NamedDecl.get_id decl in
    let b = Option.map (replace_vars sigma subst) (NamedDecl.get_value decl) in
    let t = replace_vars sigma subst (NamedDecl.get_type decl) in
    let uflags = default_flags_of TransparentState.full in
    let uflags = if flags.patvars_abstract then { uflags with allowed_evars = allow_all_but_patvars sigma } else uflags in
    let check_body sigma id c =
      match b, c with
      | Some b, Some c -> begin
         try (Evarconv.unify_delay ~flags:uflags !!env sigma b c)
         with UnableToUnify (sigma, _) ->
           user_err ?loc  (str "Cannot interpret " ++
             pr_existential_key !!env sigma evk ++
             strbrk " in current context: binding for " ++ Id.print id ++
             strbrk " is not convertible to its expected definition (cannot unify " ++
             quote (Termops.Internal.print_constr_env !!env sigma b) ++
             strbrk " and " ++
             quote (Termops.Internal.print_constr_env !!env sigma c) ++
             str ").")
         end
      | Some b, None ->
           user_err ?loc  (str "Cannot interpret " ++
             pr_existential_key !!env sigma evk ++
             strbrk " in current context: " ++ Id.print id ++
             strbrk " should be bound to a local definition.")
      | None, _ -> sigma in
    let check_type sigma id t' =
      try (Evarconv.unify_delay ~flags:uflags !!env sigma t t')
      with UnableToUnify (sigma, _) ->
        user_err ?loc  (str "Cannot interpret " ++
          pr_existential_key !!env sigma evk ++
          strbrk " in current context: binding for " ++ Id.print id ++
          strbrk " is not well-typed.") in
    let sigma, c, update =
      try
        let c = snd (List.find (fun (CAst.{v=id'},c) -> Id.equal id id') update) in
        let sigma, c = eval_pretyper self ~flags (mk_tycon t) env sigma c in
        let sigma = check_body sigma id (Some c.uj_val) in
        sigma, c.uj_val, List.remove_first (fun (CAst.{v=id'},_) -> Id.equal id id') update
      with Not_found ->
      try
        let (n,b',t') = lookup_rel_id id (rel_context !!env) in
        let sigma = check_type sigma id (lift n t') in
        let sigma = check_body sigma id (Option.map (lift n) b') in
        sigma, mkRel n, update
      with Not_found ->
      try
        let decl = lookup_named id !!env in
        let sigma = check_type sigma id (NamedDecl.get_type decl) in
        let sigma = check_body sigma id (NamedDecl.get_value decl) in
        sigma, mkVar id, update
      with Not_found ->
        user_err ?loc  (str "Cannot interpret " ++
          pr_existential_key !!env sigma evk ++
          str " in current context: no binding for " ++ Id.print id ++ str ".") in
    ((id,c)::subst, update, sigma) in
  let subst,inst,sigma = List.fold_right f hyps ([],update,sigma) in
  check_instance subst inst;
  sigma, List.map snd subst

module Default =
struct

  let discard_trace (sigma,t,otrace) = sigma, t

  let pretype_ref self (ref, u) =
    fun ?loc ~flags tycon env sigma ->
    let sigma, t_ref = pretype_ref ?loc sigma env ref u in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma t_ref tycon

  let pretype_var self id =
    fun ?loc ~flags tycon env sigma ->
    let pretype tycon env sigma t = eval_pretyper self ~flags tycon env sigma t in
    let sigma, t_id = pretype_id (fun e r t -> pretype tycon e r t) loc env sigma id in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma t_id tycon

  let pretype_evar self (CAst.{v=id;loc=locid}, inst) ?loc ~flags tycon env sigma =
      (* Ne faudrait-il pas s'assurer que hyps est bien un
         sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
      let id = interp_ltac_id env id in
      let sigma, evk =
        match Evd.evar_key id sigma with
        | evk -> sigma, evk
        | exception Not_found ->
            if flags.undeclared_evars_patvars then
              let k = Evar_kinds.(MatchingVar (FirstOrderPatVar id)) in
              let sigma, uj_val, _ = new_typed_evar env sigma ~naming:(IntroIdentifier id) ~src:(loc,k) tycon in
              sigma, fst (destEvar sigma uj_val)
            else
              error_evar_not_found ?loc:locid !!env sigma id
      in
      let EvarInfo evi = Evd.find sigma evk in
      let hyps = evar_filtered_context evi in
      let sigma, args = pretype_instance self ~flags env sigma loc hyps evk inst in
      let c = mkLEvar sigma (evk, args) in
      let j = Retyping.get_judgment_of !!env sigma c in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma j tycon

  let pretype_patvar self kind ?loc ~flags tycon env sigma =
    let k = Evar_kinds.MatchingVar kind in
    let sigma, uj_val, uj_type = new_typed_evar env sigma ~src:(loc,k) tycon in
    sigma, { uj_val; uj_type }

  let pretype_hole self k ?loc ~flags tycon env sigma =
    let open Namegen in
    let naming = naming_of_glob_kind k in
    let naming = match naming with
      | IntroIdentifier id -> IntroIdentifier (interp_ltac_id env id)
      | IntroAnonymous -> IntroAnonymous
      | IntroFresh id -> IntroFresh (interp_ltac_id env id) in
    let k = kind_of_glob_kind k in
    let sigma, uj_val, uj_type = new_typed_evar env sigma ~src:(loc,k) ~naming tycon in
    let sigma = if flags.program_mode then mark_obligation_evar sigma k uj_val else sigma in
    sigma, { uj_val; uj_type }

  let pretype_genarg self arg ?loc ~flags tycon env sigma =
    let j, sigma = GlobEnv.interp_glob_genarg ?loc ~poly:flags.poly env sigma tycon arg in
    sigma, j

  let pretype_rec self (fixkind, names, bl, lar, vdef) =
    fun ?loc ~flags tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~flags tycon env sigma c in
    let vars = VarSet.variables (Global.env ()) in
    let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
    let rec type_bl env sigma ctxt = function
      | [] -> sigma, ctxt
      | (na,_,bk,None,ty)::bl ->
        let sigma, ty' = pretype_type empty_valcon env sigma ty in
        let rty' = ESorts.relevance_of_sort ty'.utj_type in
        let dcl = LocalAssum (make_annot na rty', ty'.utj_val) in
        let dcl', env = push_rel ~hypnaming sigma dcl env in
        type_bl env sigma (Context.Rel.add dcl' ctxt) bl
      | (na,_,bk,Some bd,ty)::bl ->
        let sigma, ty' = pretype_type empty_valcon env sigma ty in
        let rty' = ESorts.relevance_of_sort ty'.utj_type in
        let sigma, bd' = pretype (mk_tycon ty'.utj_val) env sigma bd in
        let dcl = LocalDef (make_annot na rty', bd'.uj_val, ty'.utj_val) in
        let dcl', env = push_rel ~hypnaming sigma dcl env in
        type_bl env sigma (Context.Rel.add dcl' ctxt) bl in
    let sigma, ctxtv = Array.fold_left_map (fun sigma -> type_bl env sigma Context.Rel.empty) sigma bl in
    let sigma, larj =
      Array.fold_left2_map
        (fun sigma e ar ->
          pretype_type empty_valcon (snd (push_rel_context ~hypnaming sigma e env)) sigma ar)
        sigma ctxtv lar in
    let lara = Array.map (fun a -> a.utj_val) larj in
    let ftys = Array.map2 (fun e a -> it_mkProd_or_LetIn a e) ctxtv lara in
    let nbfix = Array.length lar in
    let names = Array.map (fun id -> Name id) names in
    let sigma =
      match tycon with
      | Some t ->
        let fixi = match fixkind with
          | GFix (vn,i) -> i
          | GCoFix i -> i
        in
        begin match Evarconv.unify_delay !!env sigma ftys.(fixi) t with
          | exception Evarconv.UnableToUnify _ -> sigma
          | sigma -> sigma
        end
      | None -> sigma
    in
    let names = Array.map2 (fun na t ->
        make_annot na (Retyping.relevance_of_type !!(env) sigma t))
        names ftys
    in
      (* Note: bodies are not used by push_rec_types, so [||] is safe *)
    let names,newenv = push_rec_types ~hypnaming sigma (names,ftys) env in
    let sigma, vdefj =
      Array.fold_left2_map_i
        (fun i sigma ctxt def ->
           (* we lift nbfix times the type in tycon, because of
            * the nbfix variables pushed to newenv *)
           let (ctxt,ty) =
             decompose_prod_n_decls sigma (Context.Rel.length ctxt)
               (lift nbfix ftys.(i)) in
           let ctxt,nenv = push_rel_context ~hypnaming sigma ctxt newenv in
           let sigma, j = pretype (mk_tycon ty) nenv sigma def in
           sigma, { uj_val = it_mkLambda_or_LetIn j.uj_val ctxt;
                    uj_type = it_mkProd_or_LetIn j.uj_type ctxt })
        sigma ctxtv vdef in
      let sigma = Typing.check_type_fixpoint ?loc !!env sigma names ftys vdefj in
      let nf c = nf_evar sigma c in
      let ftys = Array.map nf ftys in (* FIXME *)
      let fdefs = Array.map (fun x -> nf (j_val x)) vdefj in
      let fixj = match fixkind with
        | GFix (vn,i) ->
              (* First, let's find the guard indexes. *)
              (* If recursive argument was not given by user, we try all args.
                 An earlier approach was to look only for inductive arguments,
                 but doing it properly involves delta-reduction, and it finally
                 doesn't seem worth the effort (except for huge mutual
                 fixpoints ?) *)
          let possible_fix_indices =
            Array.to_list (Array.mapi
                             (fun i annot -> match annot with
                             | Some n -> [n]
                             | None -> List.interval 0 (Context.Rel.nhyps ctxtv.(i) - 1))
           vn)
          in
          let fixdecls = (names,ftys,fdefs) in
          let indexes = esearch_fix_guard ?loc !!env sigma possible_fix_indices fixdecls in
          make_judge (mkFix ((indexes,i),fixdecls)) ftys.(i)
        | GCoFix i ->
          let fixdecls = (names,ftys,fdefs) in
          let cofix = (i, fixdecls) in
          let () = esearch_cofix_guard ?loc !!env sigma fixdecls in
          make_judge (mkCoFix cofix) ftys.(i)
      in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma fixj tycon

  let pretype_sort self s =
    fun ?loc ~flags tycon env sigma ->
    let sigma, j = pretype_sort ?loc ~flags sigma s in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma j tycon

  let enforce_template_csts sigma (qbound,ubound) csts =
    let max_quality_opt a b = match a with
      | None -> None
      | Some a ->
        let open Sorts.Quality in
        match a, b with
        | QConstant QSProp, _ | _, QConstant QSProp -> assert false
        | QConstant QProp, q | q, QConstant QProp -> Some q
        | (QConstant QType as q), _ | _, (QConstant QType as q) -> Some q
        | QVar a', QVar b' ->
          if Sorts.QVar.equal a' b' then Some a
          else None
    in
    let sigma = ref sigma in
    let gen_max_quality qs =
      let qs = List.map (UState.nf_quality (Evd.ustate !sigma)) qs in
      match List.fold_left max_quality_opt (Some Sorts.Quality.qprop) qs with
      | Some q -> q
      | None -> match qs with
        | [] -> assert false
        | q :: rest ->
          (* all qvars or qprop with at least 2 different qvars, unify the qvars
             (alternatively: return qtype?) *)
          let mk q = ESorts.make @@ Sorts.make q Univ.Universe.type0 in
          let unify sigma q' =
            if Sorts.Quality.(equal qprop q') then sigma
            else Evd.set_eq_sort sigma (mk q) (mk q')
          in
          let sigma' = List.fold_left unify !sigma rest in
          sigma := sigma';
          q
    in
    let qbound = Int.Map.map gen_max_quality qbound in
    let sigma = !sigma in
    let bound = qbound, ubound in
    let csts = Inductive.instantiate_template_constraints bound csts in
    let sigma = Evd.add_constraints sigma csts in
    sigma, bound

  let template_sort boundus (s:Sorts.t) =
    let s = Inductive.Template.template_subst_sort boundus s in
    ESorts.make s

  let bind_template bind_sort s (qsubst,usubst) =
    let qbind, ubind = Inductive.Template.bind_kind bind_sort in
    let qsubst = match qbind with
      | None -> qsubst
      | Some qbind ->
        let sq = Sorts.quality s in
        Int.Map.update qbind (function
            | None -> Some [sq]
            | Some q0 -> Some (sq::q0))
          qsubst
    in
    let usubst = match ubind with
      | None -> usubst
      | Some ubind ->
        let u = match s with
          | SProp | Prop | Set -> Univ.Universe.type0
          | Type u | QSort (_,u) -> u
        in
        Int.Map.update ubind (function
            | None -> Some u
            | Some _ ->
              CErrors.anomaly Pp.(str "Retyping.bind_template found non linear template level."))
          usubst
    in
    qsubst, usubst

  let rec finish_template sigma boundus = let open TemplateArity in function
    | CtorType (csts, typ) ->
      let sigma, boundus = enforce_template_csts sigma boundus csts in
      sigma, typ
    | IndType (csts, ctx, s) ->
      let sigma, boundus = enforce_template_csts sigma boundus csts in
      let s = template_sort boundus s in
      sigma, mkArity (ctx, s)
    | DefParam (na, v, t, codom) ->
      let sigma, codom = finish_template sigma boundus codom in
      sigma, mkLetIn (na,v,t,codom)
    | NonTemplateArg (na,dom,codom) ->
      let sigma, codom = finish_template sigma boundus codom in
      sigma, mkProd (na,dom,codom)
    | TemplateArg (na,ctx,binder,codom) ->
      let boundus = bind_template binder.bind_sort binder.default boundus in
      let sigma, codom = finish_template sigma boundus codom in
      let s = ESorts.make @@ binder.default in
      sigma, mkProd (na,mkArity (ctx,s),codom)

  let freshen_template sigma = let open Sorts in function
    | SProp | Prop | Set -> assert false
    | Type _ ->
      let sigma, u = Evd.new_univ_level_variable UState.univ_flexible_alg sigma in
      sigma, ESorts.make (Sorts.sort_of_univ (Univ.Universe.make u))
    | QSort (q,u) ->
      let sigma, q = match Sorts.QVar.var_index q with
        | None -> sigma, q
        | Some _ ->
          let sigma, q = Evd.new_quality_variable sigma in
          let sigma = Evd.set_above_prop sigma (QVar q) in
          sigma, q
      in
      let sigma, u = match Option.bind (Univ.Universe.level u) Univ.Level.var_index with
        | None -> sigma, u
        | Some _ ->
          let sigma, u = Evd.new_univ_level_variable UState.univ_flexible_alg sigma in
          sigma, Univ.Universe.make u
      in
      sigma, ESorts.make @@ Sorts.qsort q u

  let rec apply_template pretype_arg arg_state env sigma body subst boundus todoargs typ =
    let open TemplateArity in
    match todoargs, typ with
    | [], _
    | _, (CtorType _ | IndType _) ->
      let sigma, typ = finish_template sigma boundus typ in
      sigma, body, subst, typ, arg_state, todoargs
    | _, DefParam (_, v, _, codom) ->
      (* eager subst may be inefficient but template inductives with
         letin params are hopefully rare enough that it doesn't
         matter *)
      let v = Vars.esubst Vars.lift_substituend subst v in
      let subst = Esubst.subs_cons (Vars.make_substituend v) subst in
      apply_template pretype_arg arg_state env sigma body subst boundus todoargs codom
    | arg :: todoargs, NonTemplateArg (na, dom, codom) ->
      let dom = Vars.esubst Vars.lift_substituend subst dom in
      let sigma, arg_state, body, arg = pretype_arg env sigma arg_state body arg na.binder_name dom in
      let subst = Esubst.subs_cons (Vars.make_substituend arg) subst in
      apply_template pretype_arg arg_state env sigma body subst boundus todoargs codom
    | arg :: todoargs, TemplateArg (na, ctx, binder, codom) ->
      let sigma, s = freshen_template sigma binder.bind_sort in
      let dom = Vars.esubst Vars.lift_substituend subst (mkArity (ctx, s)) in
      let sigma, arg_state, body, arg = pretype_arg env sigma arg_state body arg na.binder_name dom in
      let s =
        (* get an algebraic instead of the generated variable *)
        try
          snd @@ Reductionops.dest_arity !!env sigma @@ Retyping.get_type_of !!env sigma arg
        with Reduction.NotArity ->
          (* delayed constraints prevent getting the sort from retyping *)
          s
      in
      let boundus = bind_template binder.bind_sort (ESorts.kind sigma s) boundus in
      let subst = Esubst.subs_cons (Vars.make_substituend arg) subst in
      apply_template pretype_arg arg_state env sigma body subst boundus todoargs codom

  let pretype_app self (f, args) =
    fun ?loc ~flags tycon env sigma ->
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    let sigma, fj = pretype empty_tycon env sigma f in
    let floc = loc_of_glob_constr f in
    let length = List.length args in
    let nargs_before_bidi =
      if Option.is_empty tycon then length
      (* We apply bidirectionality hints only if an expected type is specified *)
      else
      (* if `f` is a global, we retrieve bidirectionality hints *)
        try
          let (gr,_) = destRef sigma fj.uj_val in
          Option.default length @@ get_bidirectionality_hint gr
        with DestKO ->
          length
    in
    let candargs =
      (* Bidirectional typechecking hint:
         parameters of a constructor are completely determined
         by a typing constraint *)
      (* This bidirectionality machinery is the one of `Program` for
         constructors and is orthogonal to bidirectionality hints. However, we
         could probably factorize both by providing default bidirectionality hints
         for constructors corresponding to their number of parameters. *)
      if flags.program_mode && length > 0 && isConstruct sigma fj.uj_val then
        match tycon with
        | None -> []
        | Some ty ->
          let ((ind, i), u) = destConstruct sigma fj.uj_val in
          let npars = inductive_nparams !!env ind in
          if Int.equal npars 0 then []
          else
            try
              let IndType (indf, args) = find_rectype !!env sigma ty in
              let ((ind',u'),pars) = dest_ind_family indf in
              if QInd.equal !!env ind ind' then pars
              else (* Let the usual code throw an error *) []
            with Not_found -> []
      else []
    in
    let pretype_arg ?(trace=Coercion.empty_coercion_trace) env sigma (n, val_before_bidi, bidiargs, candargs) body arg na tycon =
      (* trace is the coercion trace from coercing the body to funclass *)
      let bidi = n >= nargs_before_bidi in
      let sigma, c, bidiargs =
        if bidi then
          (* We want to get some typing information from the context
             before typing the argument, so we replace it by an
             existential variable *)
          let sigma, c_hole = new_evar env sigma ~src:(loc,Evar_kinds.InternalHole) tycon in
          sigma, c_hole, (c_hole, tycon, arg, trace) :: bidiargs
        else
          let sigma, j = pretype (Some tycon) env sigma arg in
          sigma, j_val j, bidiargs
      in
      let sigma, candargs, c =
        match candargs with
        | [] -> sigma, [], c
        | arg :: args ->
          begin match Evarconv.unify_delay !!env sigma c arg with
          | exception Evarconv.UnableToUnify (sigma,e) ->
            raise (PretypeError (!!env,sigma,CannotUnify (c, arg, Some e)))
          | sigma ->
            sigma, args, nf_evar sigma c
          end
      in
      let sigma, c = adjust_evar_source sigma na c in
      let body = Coercion.push_arg body c in
      let val_before_bidi = if bidi then val_before_bidi else body in
      sigma, (n+1,val_before_bidi,bidiargs,candargs), body, c
    in
    let rec apply_rec env sigma arg_state body (subs, typ) = function
      | [] ->
        let typ = Vars.esubst Vars.lift_substituend subs typ in
        let body = Coercion.force_app_body body in
        let resj = { uj_val = body; uj_type = typ } in
        let _,val_before_bidi, bidiargs,_ = arg_state in
        sigma, resj, val_before_bidi, List.rev bidiargs
      | c::rest ->
        let argloc = loc_of_glob_constr c in
        let sigma, body, na, c1, subs, c2, trace = match EConstr.kind sigma typ with
        | Prod (na, c1, c2) ->
          (* Fast path *)
          let c1 = Vars.esubst Vars.lift_substituend subs c1 in
          sigma, body, na, c1, subs, c2, Coercion.empty_coercion_trace
        | _ ->
          let typ = Vars.esubst Vars.lift_substituend subs typ in
          let sigma, body, typ, trace = Coercion.inh_app_fun ~program_mode:flags.program_mode ~resolve_tc:flags.resolve_tc ~use_coercions:flags.use_coercions !!env sigma body typ in
          let resty = whd_all !!env sigma typ in
          let na, c1, c2 = match EConstr.kind sigma resty with
          | Prod (na, c1, c2) -> (na, c1, c2)
          | _ ->
            let sigma, hj = pretype empty_tycon env sigma c in
            let resj = { uj_val = Coercion.force_app_body body; uj_type = typ } in
            error_cant_apply_not_functional
              ?loc:(Loc.merge_opt floc argloc) !!env sigma resj [|hj|]
          in
          sigma, body, na, c1, Esubst.subs_id 0, c2, trace
        in
        let sigma, arg_state, body, arg =
          pretype_arg env sigma arg_state ~trace body c na.binder_name c1
        in
        let subs = Esubst.subs_cons (Vars.make_substituend arg) subs in
        apply_rec env sigma arg_state body (subs, c2) rest
    in
    let body = (Coercion.start_app_body sigma fj.uj_val) in
    let sigma, template_arity = match EConstr.kind sigma fj.uj_val with
      | Ind (ind,u) | Construct ((ind,_),u) as k
        when EInstance.is_empty u && Environ.template_polymorphic_ind ind !!env ->
        let ctoropt = match k with
          | Ind _ -> None
          | Construct ((_,ctor),_) -> Some ctor
          | _ -> assert false
        in
        let arity = TemplateArity.get_template_arity !!env ind ~ctoropt in
        sigma, Some arity
      | _ -> sigma, None
    in
    let arg_state = (0,body,[],candargs) in
    let subst =  Esubst.subs_id 0 in
    let typ = fj.uj_type in
    let sigma, body, subst, typ, arg_state, args =
      match template_arity with
      | None -> sigma, body, subst, typ, arg_state, args
      | Some typ ->
        let pretype_arg env sigma arg_state body arg na tycon =
          pretype_arg env sigma arg_state body arg na tycon
        in
        apply_template pretype_arg arg_state env sigma body subst (Int.Map.empty,Int.Map.empty) args typ
    in
    let sigma, resj, val_before_bidi, bidiargs =
      apply_rec env sigma arg_state body (subst,typ) args
    in
    let sigma, resj, otrace = inh_conv_coerce_to_tycon ?loc ~flags env sigma resj tycon in
    let refine_arg (sigma,t) (newarg,ty,origarg,trace) =
      (* Refine an argument (originally `origarg`) represented by an evar
         (`newarg`) to use typing information from the context *)
      (* Type the argument using the expected type *)
      let sigma, j = pretype (Some ty) env sigma origarg in
      (* Unify the (possibly refined) existential variable with the
         (typechecked) original value *)
      let sigma = try Evarconv.unify_delay !!env sigma newarg (j_val j)
        with Evarconv.UnableToUnify (sigma,e) ->
          raise (PretypeError (!!env,sigma,CannotUnify (newarg,j_val j,Some e)))
      in
      sigma, Coercion.push_arg (Coercion.reapply_coercions_body sigma trace t) (j_val j)
    in
    (* We now refine any arguments whose typing was delayed for
       bidirectionality *)
    let t = val_before_bidi in
    let sigma, t = List.fold_left refine_arg (sigma,t) bidiargs in
    let t = Coercion.force_app_body t in
    (* If we did not get a coercion trace (e.g. with `Program` coercions, we
       replaced user-provided arguments with inferred ones. Otherwise, we apply
       the coercion trace to the user-provided arguments. *)
    let resj =
      match otrace with
      | None -> resj
      | Some trace ->
        let resj = { resj with uj_val = t } in
        { resj with uj_val = Coercion.reapply_coercions sigma trace t }
    in
    (sigma, resj)

  let pretype_proj self ((f,us), args, c) =
    fun ?loc ~flags tycon env sigma ->
    pretype_app self (DAst.make ?loc (GRef (GlobRef.ConstRef f,us)), args @ [c])
      ?loc ~flags tycon env sigma

  let pretype_lambda self (name, bk, c1, c2) =
    fun ?loc ~flags tycon env sigma ->
    let open Context.Rel.Declaration in
    let tycon' = if flags.program_mode && flags.use_coercions
      then Option.map (Coercion.remove_subset !!env sigma) tycon
      else tycon
    in
    let sigma,name',dom,rng =
      match tycon' with
      | None -> sigma,Anonymous, None, None
      | Some ty ->
        let sigma, ty = Evardefine.presplit !!env sigma ty in
        match EConstr.kind sigma ty with
        | Prod (na,dom,rng) ->
          sigma, na.binder_name, Some dom, Some rng
        | Evar ev ->
          (* define_evar_as_product works badly when impredicativity
             is possible but not known (#12623). OTOH if we know we
             are impredicative (typically Prop) we want to keep the
             information when typing the body. *)
          let s = Retyping.get_sort_of !!env sigma ty in
          if Environ.is_impredicative_sort !!env (ESorts.kind sigma s)
             || Evd.check_leq sigma ESorts.type1 s
          then
            let sigma, prod = define_evar_as_product !!env sigma ev in
            let na,dom,rng = destProd sigma prod in
            sigma, na.binder_name, Some dom, Some rng
          else
            sigma, Anonymous, None, None
        | _ ->
          if Reductionops.is_head_evar !!env sigma ty then sigma, Anonymous, None, None
          else
            (* No chance of unifying with a product.
               NB: Funclass cannot be a source class so no coercions. *)
            error_not_product ?loc !!env sigma ty
    in
    let dom_valcon = valcon_of_tycon dom in
    let sigma, j = eval_type_pretyper self ~flags dom_valcon env sigma c1 in
    let name = {binder_name=name; binder_relevance=ESorts.relevance_of_sort j.utj_type} in
    let var = LocalAssum (name, j.utj_val) in
    let vars = VarSet.variables (Global.env ()) in
    let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
    let var',env' = push_rel ~hypnaming sigma var env in
    let sigma, j' = eval_pretyper self ~flags rng env' sigma c2 in
    let name = get_name var' in
    let resj = judge_of_abstraction !!env sigma (orelse_name name name') j j' in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma resj tycon

  let pretype_prod self (name, bk, c1, c2) =
    fun ?loc ~flags tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~flags tycon env sigma c in
    let sigma, j = pretype_type empty_valcon env sigma c1 in
    let vars = VarSet.variables (Global.env ()) in
    let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
    let sigma, name, j' = match name with
      | Anonymous ->
        let sigma, j = pretype_type empty_valcon env sigma c2 in
        sigma, name, { j with utj_val = lift 1 j.utj_val }
      | Name _ ->
        let r = ESorts.relevance_of_sort j.utj_type in
        let var = LocalAssum (make_annot name r, j.utj_val) in
        let var, env' = push_rel ~hypnaming sigma var env in
        let sigma, c2_j = pretype_type empty_valcon env' sigma c2 in
        sigma, get_name var, c2_j
    in
    let resj =
      try
        judge_of_product !!env sigma name j j'
      with TypeError _ as e ->
        let (e, info) = Exninfo.capture e in
        let info = Option.cata (Loc.add_loc info) info loc in
        Exninfo.iraise (e, info) in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma resj tycon

  let pretype_letin self (name, c1, t, c2) =
    fun ?loc ~flags tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~flags tycon env sigma c in
    let sigma, tycon1 =
      match t with
      | Some t ->
        let sigma, t_j = pretype_type empty_valcon env sigma t in
        sigma, mk_tycon t_j.utj_val
      | None ->
        sigma, empty_tycon in
    let sigma, j = pretype tycon1 env sigma c1 in
    let sigma, t = Evarsolve.refresh_universes
      ~onlyalg:true ~status:Evd.univ_flexible (Some false) !!env sigma j.uj_type in
    let r = Retyping.relevance_of_term !!env sigma j.uj_val in
    let var = LocalDef (make_annot name r, j.uj_val, t) in
    let tycon = lift_tycon 1 tycon in
    let vars = VarSet.variables (Global.env ()) in
    let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
    let var, env = push_rel ~hypnaming sigma var env in
    let sigma, j' = pretype tycon env sigma c2 in
    let name = get_name var in
    sigma, { uj_val = mkLetIn (make_annot name r, j.uj_val, t, j'.uj_val) ;
             uj_type = subst1 j.uj_val j'.uj_type }

  let pretype_lettuple self (nal, (na, po), c, d) =
    fun ?loc ~flags tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~flags tycon env sigma c in
    let sigma, cj = pretype empty_tycon env sigma c in
    let (IndType (indf,realargs)) as indty =
      try find_rectype !!env sigma cj.uj_type
      with Not_found ->
        let cloc = loc_of_glob_constr c in
          error_case_not_inductive ?loc:cloc !!env sigma cj
    in
    let ind = fst (fst (dest_ind_family indf)) in
    let cstrs = get_constructors !!env indf in
    if not (Int.equal (Array.length cstrs) 1) then
      user_err ?loc  (str "Destructing let is only for inductive types" ++
        str " with one constructor.");
    let cs = cstrs.(0) in
    if not (Int.equal (List.length nal) cs.cs_nargs) then
      user_err ?loc:loc (str "Destructing let on this type expects " ++
        int cs.cs_nargs ++ str " variables.");
    let fsign, record =
      match Environ.get_projections !!env ind with
      | None ->
         List.map2 set_name (List.rev nal) cs.cs_args, false
      | Some ps ->
        let rec aux n k names l =
          match names, l with
          | na :: names, (LocalAssum (na', t) :: l) ->
            let proj = Projection.make (fst ps.(cs.cs_nargs - k)) true in
            LocalDef ({na' with binder_name = na},
                      lift (cs.cs_nargs - n) (mkProj (proj, na'.binder_relevance, cj.uj_val)), t)
            :: aux (n+1) (k + 1) names l
          | na :: names, (decl :: l) ->
            set_name na decl :: aux (n+1) k names l
          | [], [] -> []
          | _ -> assert false
        in aux 1 1 (List.rev nal) cs.cs_args, true in
    let fsign = Context.Rel.map (whd_betaiota !!env sigma) fsign in
    let vars = VarSet.variables (Global.env ()) in
    let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
    let fsign,env_f = push_rel_context ~hypnaming sigma fsign env in
    let obj indt rci p v f =
      if not record then
        let f = it_mkLambda_or_LetIn f fsign in
        let ci = make_case_info !!env (ind_of_ind_type indt) LetStyle in
          mkCase (EConstr.contract_case !!env sigma (ci, (p,rci), make_case_invert !!env sigma indt ~case_relevance:rci ci, cj.uj_val,[|f|]))
      else it_mkLambda_or_LetIn f fsign
    in
    (* Make dependencies from arity signature impossible *)
    let arsgn, indr =
      let arsgn = get_arity !!env indf in
      List.map (set_name Anonymous) arsgn, Inductiveops.relevance_of_inductive_family !!env indf
    in
      let indt = build_dependent_inductive !!env indf in
      let psign = LocalAssum (make_annot na indr, indt) :: arsgn in (* For locating names in [po] *)
      let predenv = Cases.make_return_predicate_ltac_lvar env sigma na c cj.uj_val in
      let nar = List.length arsgn in
      let psign',env_p = push_rel_context ~hypnaming ~force_names:true sigma psign predenv in
          (match po with
          | Some p ->
            let sigma, pj = pretype_type empty_valcon env_p sigma p in
            let ccl = nf_evar sigma pj.utj_val in
            let p = it_mkLambda_or_LetIn ccl psign' in
            let inst =
              (Array.to_list cs.cs_concl_realargs)
              @ [build_dependent_constructor cs] in
            let lp = lift cs.cs_nargs p in
            let fty = hnf_lam_applist !!env sigma lp inst in
            let sigma, fj = pretype (mk_tycon fty) env_f sigma d in
            let sigma, v =
              let ind,_ = dest_ind_family indf in
                let sigma, rci = Typing.check_allowed_sort !!env sigma ind cj.uj_val p in
                sigma, obj indty rci p cj.uj_val fj.uj_val
            in
            sigma, { uj_val = v; uj_type = (substl (realargs@[cj.uj_val]) ccl) }

          | None ->
            let tycon = lift_tycon cs.cs_nargs tycon in
            let sigma, fj = pretype tycon env_f sigma d in
            let ccl = nf_evar sigma fj.uj_type in
            let ccl =
              if noccur_between sigma 1 cs.cs_nargs ccl then
                lift (- cs.cs_nargs) ccl
              else
                error_cant_find_case_type ?loc !!env sigma
                  cj.uj_val in
                 (* let ccl = refresh_universes ccl in *)
            let p = it_mkLambda_or_LetIn (lift (nar+1) ccl) psign' in
            let sigma, v =
              let ind,_ = dest_ind_family indf in
                let sigma, rci = Typing.check_allowed_sort !!env sigma ind cj.uj_val p in
                sigma, obj indty rci p cj.uj_val fj.uj_val
            in sigma, { uj_val = v; uj_type = ccl })

  let pretype_cases self (sty, po, tml, eqns)  =
    fun ?loc ~flags tycon env sigma ->
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    Cases.compile_cases ?loc ~program_mode:flags.program_mode sty (pretype, sigma) tycon env (po,tml,eqns)

  let pretype_if self (c, (na, po), b1, b2) =
    fun ?loc ~flags tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    let sigma, cj = pretype empty_tycon env sigma c in
    let (IndType (indf,realargs)) as indty =
      try find_rectype !!env sigma cj.uj_type
      with Not_found ->
        let cloc = loc_of_glob_constr c in
          error_case_not_inductive ?loc:cloc !!env sigma cj in
    let cstrs = get_constructors !!env indf in
      if not (Int.equal (Array.length cstrs) 2) then
        user_err ?loc
                      (str "If is only for inductive types with two constructors.");

      let arsgn, indr =
        let arsgn = get_arity !!env indf in
        (* Make dependencies from arity signature impossible *)
        List.map (set_name Anonymous) arsgn, Inductiveops.relevance_of_inductive_family !!env indf
      in
      let nar = List.length arsgn in
      let indt = build_dependent_inductive !!env indf in
      let psign = LocalAssum (make_annot na indr, indt) :: arsgn in (* For locating names in [po] *)
      let predenv = Cases.make_return_predicate_ltac_lvar env sigma na c cj.uj_val in
      let vars = VarSet.variables (Global.env ()) in
      let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
      let psign,env_p = push_rel_context ~hypnaming sigma psign predenv in
      let sigma, pred, p = match po with
        | Some p ->
          let sigma, pj = eval_type_pretyper self ~flags empty_valcon env_p sigma p in
          let ccl = nf_evar sigma pj.utj_val in
          let pred = it_mkLambda_or_LetIn ccl psign in
          let typ = lift (- nar) (beta_applist sigma (pred,[cj.uj_val])) in
          sigma, pred, typ
        | None ->
          let sigma, p = match tycon with
            | Some ty -> sigma, ty
            | None -> new_type_evar env sigma ~src:(loc,Evar_kinds.CasesType false)
          in
          sigma, it_mkLambda_or_LetIn (lift (nar+1) p) psign, p in
      let pred = nf_evar sigma pred in
      let p = nf_evar sigma p in
      let f sigma cs b =
        let n = Context.Rel.length cs.cs_args in
        let pi = lift n pred in (* liftn n 2 pred ? *)
        let pi = beta_applist sigma (pi, [build_dependent_constructor cs]) in
        let cs_args = cs.cs_args in
        let cs_args = Context.Rel.map (whd_betaiota !!env sigma) cs_args in
        let csgn =
          List.map (set_name Anonymous) cs_args
        in
        let _,env_c = push_rel_context ~hypnaming sigma csgn env in
        let sigma, bj = pretype (mk_tycon pi) env_c sigma b in
        sigma, it_mkLambda_or_LetIn bj.uj_val cs_args in
      let sigma, b1 = f sigma cstrs.(0) b1 in
      let sigma, b2 = f sigma cstrs.(1) b2 in
      let sigma, v =
        let ind,_ = dest_ind_family indf in
        let pred = nf_evar sigma pred in
        let sigma, rci = Typing.check_allowed_sort !!env sigma ind cj.uj_val pred in
        let ci = make_case_info !!env (fst ind) IfStyle in
        sigma, mkCase (EConstr.contract_case !!env sigma
                  (ci, (pred,rci),
                   make_case_invert !!env sigma indty ~case_relevance:rci ci, cj.uj_val,
                   [|b1;b2|]))
      in
      let cj = { uj_val = v; uj_type = p } in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma cj tycon

  let pretype_cast self (c, k, t) =
    fun ?loc ~flags tycon env sigma ->
    let pretype tycon env sigma c = eval_pretyper self ~flags tycon env sigma c in
    let sigma, cj =
      let sigma, tj = eval_type_pretyper self ~flags empty_valcon env sigma t in
      let tval = nf_evar sigma tj.utj_val in
      let (sigma, cj), tval = match k with
        | Some VMcast ->
          let sigma, cj = pretype empty_tycon env sigma c in
          let cty = nf_evar sigma cj.uj_type and tval = nf_evar sigma tval in
          begin match Reductionops.vm_infer_conv !!env sigma cty tval with
            | Some sigma -> (sigma, cj), tval
            | None ->
              error_actual_type ?loc !!env sigma cj tval
                (ConversionFailed (!!env,cty,tval))
          end
        | Some NATIVEcast ->
          let sigma, cj = pretype empty_tycon env sigma c in
          let cty = nf_evar sigma cj.uj_type and tval = nf_evar sigma tval in
          begin
            match Reductionops.native_infer_conv !!env sigma cty tval with
            | Some sigma -> (sigma, cj), tval
            | None ->
              error_actual_type ?loc !!env sigma cj tval
                (ConversionFailed (!!env,cty,tval))
          end
        | None | Some DEFAULTcast ->
          pretype (mk_tycon tval) env sigma c, tval
      in
      let v = match k with
        | None -> cj.uj_val
        | Some k -> mkCast (cj.uj_val, k, tval)
      in
      sigma, { uj_val = v; uj_type = tval }
    in discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma cj tycon

(* [pretype_type valcon env sigma c] coerces [c] into a type *)
let pretype_type self c ?loc ~flags valcon (env : GlobEnv.t) sigma = match DAst.get c with
  | GHole knd ->
      let loc = loc_of_glob_constr c in
      let naming = naming_of_glob_kind knd in
      let knd = kind_of_glob_kind knd in
      (match valcon with
       | Some v ->
           let sigma, s =
             let t = Retyping.get_type_of !!env sigma v in
               match EConstr.kind sigma (whd_all !!env sigma t) with
               | Sort s ->
                 sigma, s
               | Evar ev when is_Type sigma (existential_type sigma ev) ->
                 define_evar_as_sort !!env sigma ev
               | _ -> anomaly (Pp.str "Found a type constraint which is not a type.")
           in
           (* Correction of bug #5315 : we need to define an evar for *all* holes *)
           let sigma, evkt = new_evar env sigma ~src:(loc, knd) ~naming (mkSort s) in
           let ev,_ = destEvar sigma evkt in
           let sigma = Evd.define ev (nf_evar sigma v) sigma in
           (* End of correction of bug #5315 *)
           sigma, { utj_val = v;
                    utj_type = s }
       | None ->
         let sigma, s = new_sort_variable univ_flexible_alg sigma in
         let sigma, utj_val = new_evar env sigma ~src:(loc, knd) ~naming (mkSort s) in
         let sigma = if flags.program_mode then mark_obligation_evar sigma knd utj_val else sigma in
         sigma, { utj_val; utj_type = s})
  | _ ->
      let sigma, j = eval_pretyper self ~flags empty_tycon env sigma c in
      let loc = loc_of_glob_constr c in
      let sigma, tj =
        let use_coercions = flags.use_coercions in
        Coercion.inh_coerce_to_sort ?loc ~use_coercions !!env sigma j in
      match valcon with
      | None -> sigma, tj
      | Some v ->
        begin match Evarconv.unify_leq_delay !!env sigma v tj.utj_val with
        | sigma -> sigma, tj
        | exception Evarconv.UnableToUnify (sigma,e) ->
          error_unexpected_type
            ?loc:(loc_of_glob_constr c) !!env sigma tj.utj_val v e
        end

  let pretype_int self i =
    fun ?loc ~flags tycon env sigma ->
        let resj =
          try Typing.judge_of_int !!env i
          with Invalid_argument _ ->
            user_err ?loc (str "Type of int63 should be registered first.")
        in
        discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma resj tycon

  let pretype_float self f =
    fun ?loc ~flags tycon env sigma ->
      let resj =
        try Typing.judge_of_float !!env f
        with Invalid_argument _ ->
          user_err ?loc (str "Type of float should be registered first.")
        in
        discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma resj tycon

  let pretype_string self s =
    fun ?loc ~flags tycon env sigma ->
      let resj =
        try Typing.judge_of_string !!env s
        with Invalid_argument _ ->
          user_err ?loc (str "Type of string should be registered first.")
        in
        discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma resj tycon

  let pretype_array self (u,t,def,ty) =
    fun ?loc ~flags tycon env sigma ->
    let array_kn = match (Environ.retroknowledge !!env).Retroknowledge.retro_array with
  | Some c -> c
  | None -> CErrors.user_err Pp.(str"The type array must be registered before this construction can be typechecked.")
    in
    let sigma, u = match u with
      | None -> sigma, None
      | Some ([],[u]) ->
        let sigma, u = glob_level ?loc sigma u in
        sigma, Some u
      | Some (qs,us) ->
        let open UnivGen in
          Loc.raise ?loc (UniverseLengthMismatch {
            gref = ConstRef array_kn;
            actual = List.length qs, List.length us;
            expect = 0, 1;
          })
    in
    let sigma, tycon' = split_as_array !!env sigma tycon in
    let sigma, jty = eval_type_pretyper self ~flags tycon' env sigma ty in
    let sigma, jdef = eval_pretyper self ~flags (mk_tycon jty.utj_val) env sigma def in
    let pretype_elem = eval_pretyper self ~flags (mk_tycon jty.utj_val) env in
    let sigma, jt = Array.fold_left_map pretype_elem sigma t in
    let sigma, u = match u with
      | Some u -> sigma, u
      | None -> Evd.new_univ_level_variable UState.univ_flexible sigma
    in
    let sigma = Evd.set_leq_sort sigma
        (* we retype because it may be an evar which has been defined, resulting in a lower sort
           cf #18480 *)
        (Retyping.get_sort_of !!env sigma jty.utj_val)
        (ESorts.make (Sorts.sort_of_univ (Univ.Universe.make u)))
    in
    let u = UVars.Instance.of_array ([||],[| u |]) in
    let ta = EConstr.mkConstU (array_kn, EInstance.make u) in
    let j = {
      uj_val = EConstr.mkArray(EInstance.make u, Array.map (fun j -> j.uj_val) jt, jdef.uj_val, jty.utj_val);
      uj_type = EConstr.mkApp(ta,[|jdef.uj_type|])
    } in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~flags env sigma j tycon

end

(* [pretype tycon env sigma lvar lmeta cstr] attempts to type [cstr] *)
(* in environment [env], with existential variables [sigma] and *)
(* the type constraint tycon *)

let default_pretyper =
  let open Default in
  {
    pretype_ref = pretype_ref;
    pretype_var = pretype_var;
    pretype_evar = pretype_evar;
    pretype_patvar = pretype_patvar;
    pretype_app = pretype_app;
    pretype_proj = pretype_proj;
    pretype_lambda = pretype_lambda;
    pretype_prod = pretype_prod;
    pretype_letin = pretype_letin;
    pretype_cases = pretype_cases;
    pretype_lettuple = pretype_lettuple;
    pretype_if = pretype_if;
    pretype_rec = pretype_rec;
    pretype_sort = pretype_sort;
    pretype_hole = pretype_hole;
    pretype_genarg = pretype_genarg;
    pretype_cast = pretype_cast;
    pretype_int = pretype_int;
    pretype_float = pretype_float;
    pretype_string = pretype_string;
    pretype_array = pretype_array;
    pretype_type = pretype_type;
  }

let pretype ~flags tycon env sigma c =
  eval_pretyper default_pretyper ~flags tycon env sigma c

let pretype_type ~flags tycon env sigma c =
  eval_type_pretyper default_pretyper ~flags tycon env sigma c

let ise_pretype_gen (flags : inference_flags) env sigma lvar kind c =
  let pretype_flags = {
    program_mode = flags.program_mode;
    use_coercions = flags.use_coercions;
    poly = flags.polymorphic;
    undeclared_evars_patvars = flags.undeclared_evars_patvars;
    patvars_abstract = flags.patvars_abstract;
    unconstrained_sorts = flags.unconstrained_sorts;
    resolve_tc = match flags.use_typeclasses with
      | NoUseTC -> false
      | UseTC | UseTCForConv -> true
  } in
  let vars = VarSet.variables (Global.env ()) in
  let hypnaming = if flags.program_mode then ProgramNaming vars else RenameExistingBut vars in
  let env = GlobEnv.make ~hypnaming env sigma lvar in
  let sigma', c', c'_ty = match kind with
    | WithoutTypeConstraint ->
      let sigma, j = pretype ~flags:pretype_flags empty_tycon env sigma c in
      sigma, j.uj_val, j.uj_type
    | OfType exptyp ->
      let sigma, j = pretype ~flags:pretype_flags (mk_tycon exptyp) env sigma c in
      sigma, j.uj_val, j.uj_type
    | IsType ->
      let sigma, tj = pretype_type ~flags:pretype_flags empty_valcon env sigma c in
      sigma, tj.utj_val, mkSort tj.utj_type
  in
  process_inference_flags flags !!env sigma (sigma',c',c'_ty)

let ise_pretype_gen flags env sigma lvar kind c : _ * _ * _ =
  NewProfile.profile "pretyping" (fun () ->
      ise_pretype_gen flags env sigma lvar kind c)
    ()

let default_inference_flags fail = {
  use_coercions = true;
  use_typeclasses = UseTC;
  solve_unification_constraints = true;
  fail_evar = fail;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
  undeclared_evars_patvars = false;
  patvars_abstract = false;
  unconstrained_sorts = false;
}

let no_classes_no_fail_inference_flags = {
  use_coercions = true;
  use_typeclasses = NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
  undeclared_evars_patvars = false;
  patvars_abstract = false;
  unconstrained_sorts = false;
}

let all_and_fail_flags = default_inference_flags true
let all_no_fail_flags = default_inference_flags false

let ise_pretype_gen_ctx flags env sigma lvar kind c =
  let sigma, c, _ = ise_pretype_gen flags env sigma lvar kind c in
  c, Evd.ustate sigma

(** Entry points of the high-level type synthesis algorithm *)

let understand
    ?(flags=all_and_fail_flags)
    ?(expected_type=WithoutTypeConstraint)
    env sigma c =
  ise_pretype_gen_ctx flags env sigma empty_lvar expected_type c

let understand_tcc_ty ?(flags=all_no_fail_flags) env sigma ?(expected_type=WithoutTypeConstraint) c =
  ise_pretype_gen flags env sigma empty_lvar expected_type c

let understand_tcc ?flags env sigma ?expected_type c =
  let sigma, c, _ = understand_tcc_ty ?flags env sigma ?expected_type c in
  sigma, c

let understand_ltac flags env sigma lvar kind c =
  let (sigma, c, _) = ise_pretype_gen flags env sigma lvar kind c in
  (sigma, c)

let understand_ltac_ty flags env sigma lvar kind c =
  ise_pretype_gen flags env sigma lvar kind c

(* Fully evaluate an untyped constr *)
let understand_uconstr ?(flags = all_and_fail_flags)
  ?(expected_type = WithoutTypeConstraint) env sigma c =
  let open Ltac_pretype in
  let { closure; term } = c in
  let vars = {
    ltac_constrs = closure.typed;
    ltac_uconstrs = closure.untyped;
    ltac_idents = closure.idents;
    ltac_genargs = closure.genargs;
  } in
  understand_ltac flags env sigma vars expected_type term

let path_convertible env sigma cl p q =
  let open Coercionops in
  let mkGRef ref          = DAst.make @@ Glob_term.GRef(ref,None) in
  let mkGVar id           = DAst.make @@ Glob_term.GVar(id) in
  let mkGApp(rt,rtl)      = DAst.make @@ Glob_term.GApp(rt,rtl) in
  let mkGLambda(n,t,b)    = DAst.make @@ Glob_term.GLambda(n,None,Explicit,t,b) in
  let mkGSort u           = DAst.make @@ Glob_term.GSort u in
  let mkGHole ()          = DAst.make @@ Glob_term.GHole (GBinderType Anonymous) in
  let path_to_gterm p =
    match p with
    | ic :: p' ->
      let names =
        List.init (ic.coe_param + 1)
          (fun n -> Id.of_string ("x" ^ string_of_int n))
      in
      List.fold_right
        (fun id t -> mkGLambda (Name id, mkGHole (), t)) names @@
        List.fold_left
          (fun t ic ->
             mkGApp (mkGRef ic.coe_value,
                     List.make ic.coe_param (mkGHole ()) @ [t]))
          (mkGApp (mkGRef ic.coe_value, List.map mkGVar names))
          p'
    | [] ->
      (* identity function for the class [i]. *)
      let params = class_nparams cl in
      let clty =
        match cl with
        | CL_SORT -> mkGSort (None, Glob_term.UAnonymous {rigid=UnivFlexible false})
        | CL_FUN -> anomaly (str "A source class must not be Funclass.")
        | CL_SECVAR v -> mkGRef (GlobRef.VarRef v)
        | CL_CONST c -> mkGRef (GlobRef.ConstRef c)
        | CL_IND i -> mkGRef (GlobRef.IndRef i)
        | CL_PROJ p -> mkGRef (GlobRef.ConstRef (Projection.Repr.constant p))
      in
      let names =
        List.init params (fun n -> Id.of_string ("x" ^ string_of_int n))
      in
      List.fold_right
        (fun id t -> mkGLambda (Name id, mkGHole (), t)) names @@
        mkGLambda (Name (Id.of_string "x"),
                   mkGApp (clty, List.map mkGVar names),
                   mkGVar (Id.of_string "x"))
  in
  try
    let sigma,tp = understand_tcc env sigma (path_to_gterm p) in
    let sigma,tq = understand_tcc env sigma (path_to_gterm q) in
    if Evd.has_undefined sigma then
      false
    else
      let _ = Evarconv.unify_delay env sigma tp tq in true
  with Evarconv.UnableToUnify _ | PretypeError _ -> false

let () = Coercionops.install_path_comparator path_convertible
