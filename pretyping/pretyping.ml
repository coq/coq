(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

type typing_constraint = UnknownIfTermOrType | IsType | OfType of types | WithoutTypeConstraint

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

(* An auxiliary function for searching for fixpoint guard indexes *)

exception Found of int array

let nf_fix sigma (nas, cs, ts) =
  let inj c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  (nas, Array.map inj cs, Array.map inj ts)

let search_guard ?loc env possible_indexes fixdefs =
  (* Standard situation with only one possibility for each fix. *)
  (* We treat it separately in order to get proper error msg. *)
  let is_singleton = function [_] -> true | _ -> false in
  if List.for_all is_singleton possible_indexes then
    let indexes = Array.of_list (List.map List.hd possible_indexes) in
    let fix = ((Array.map (fun i -> Some i) indexes, 0),fixdefs) in
    (try check_fix env fix
     with reraise ->
       let (e, info) = Exninfo.capture reraise in
       let info = Option.cata (fun loc -> Loc.add_loc info loc) info loc in
       Exninfo.iraise (e, info));
    indexes
  else
    (* we now search recursively among all combinations *)
    (try
       List.iter
         (fun l ->
            let indexes = Array.of_list l in
            let fix = ((Array.map (fun i -> Some i) indexes, 0),fixdefs) in
            (* spiwack: We search for a unspecified structural
               argument under the assumption that we need to check the
               guardedness condition (otherwise the first inductive argument
               will be chosen). A more robust solution may be to raise an
               error when totality is assumed but the strutural argument is
               not specified. *)
            try
              let flags = { (typing_flags env) with Declarations.check_guarded = true } in
              let env = Environ.set_typing_flags flags env in
              check_fix env fix; raise (Found indexes)
            with TypeError _ -> ())
         (List.combinations possible_indexes);
       let errmsg = "Cannot guess decreasing argument of fix." in
         user_err ?loc ~hdr:"search_guard" (Pp.str errmsg)
     with Found indexes -> indexes)

let esearch_guard ?loc env sigma indexes fix =
  let fix = nf_fix sigma fix in
  try search_guard ?loc env indexes fix
  with TypeError (env,err) ->
    raise (PretypeError (env,sigma,TypingError (map_ptype_error of_constr err)))

(* To force universe name declaration before use *)

let is_strict_universe_declarations =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Strict";"Universe";"Declaration"]
    ~value:true

(** Miscellaneous interpretation functions *)

let interp_known_universe_level_name evd qid =
  try
    let open Libnames in
    if qualid_is_ident qid then Evd.universe_of_name evd @@ qualid_basename qid
    else raise Not_found
  with Not_found ->
    let qid = Nametab.locate_universe qid in
    Univ.Level.make qid

let interp_universe_level_name ~anon_rigidity evd qid =
  try evd, interp_known_universe_level_name evd qid
  with Not_found ->
    if Libnames.qualid_is_ident qid then (* Undeclared *)
      let id = Libnames.qualid_basename qid in
      if not (is_strict_universe_declarations ()) then
        new_univ_level_variable ?loc:qid.CAst.loc ~name:id univ_rigid evd
      else user_err ?loc:qid.CAst.loc ~hdr:"interp_universe_level_name"
          (Pp.(str "Undeclared universe: " ++ Id.print id))
    else
      let dp, i = Libnames.repr_qualid qid in
      let num =
        try int_of_string (Id.to_string i)
        with Failure _ ->
          user_err ?loc:qid.CAst.loc ~hdr:"interp_universe_level_name"
            (Pp.(str "Undeclared global universe: " ++ Libnames.pr_qualid qid))
      in
      let level = Univ.Level.(make (UGlobal.make dp num)) in
      let evd =
        try Evd.add_global_univ evd level
        with UGraph.AlreadyDeclared -> evd
      in evd, level

let interp_universe_name ?loc evd l =
  (* [univ_flexible_alg] can produce algebraic universes in terms *)
  let anon_rigidity = univ_flexible in
  let evd', l = interp_universe_level_name ~anon_rigidity evd l in
  evd', l

let interp_sort_name ?loc sigma = function
  | GSProp -> sigma, Univ.Level.sprop
  | GProp -> sigma, Univ.Level.prop
  | GSet -> sigma, Univ.Level.set
  | GType l -> interp_universe_name ?loc sigma l

let interp_sort_info ?loc evd l =
    List.fold_left (fun (evd, u) (l,n) ->
      let evd', u' = interp_sort_name ?loc evd l in
      let u' = Univ.Universe.make u' in
      let u' = match n with
      | 0 -> u'
      | 1 -> Univ.Universe.super u'
      | n ->
        user_err ?loc ~hdr:"interp_universe"
          (Pp.(str "Cannot interpret universe increment +" ++ int n))
      in (evd', Univ.sup u u'))
    (evd, Univ.Universe.type0m) l

type inference_hook = env -> evar_map -> Evar.t -> (evar_map * constr) option

type use_typeclasses = NoUseTC | UseTCForConv | UseTC

type inference_flags = {
  use_typeclasses : use_typeclasses;
  solve_unification_constraints : bool;
  fail_evar : bool;
  expand_evars : bool;
  program_mode : bool;
  polymorphic : bool;
}

(* Compute the set of still-undefined initial evars up to restriction
   (e.g. clearing) and the set of yet-unsolved evars freshly created
   in the extension [sigma'] of [sigma] (excluding the restrictions of
   the undefined evars of [sigma] to be freshly created evars of
   [sigma']). Otherwise said, we partition the undefined evars of
   [sigma'] into those already in [sigma] or deriving from an evar in
   [sigma] by restriction, and the evars properly created in [sigma'] *)

type frozen =
| FrozenId of evar_info Evar.Map.t
  (** No pending evars. We do not put a set here not to reallocate like crazy,
      but the actual data of the map is not used, only keys matter. All
      functions operating on this type must have the same behaviour on
      [FrozenId map] and [FrozenProgress (Evar.Map.domain map, Evar.Set.empty)] *)
| FrozenProgress of (Evar.Set.t * Evar.Set.t) Lazy.t
  (** Proper partition of the evar map as described above. *)

let frozen_and_pending_holes (sigma, sigma') =
  let undefined0 = Option.cata Evd.undefined_map Evar.Map.empty sigma in
  (* Fast path when the undefined evars where not modified *)
  if undefined0 == Evd.undefined_map sigma' then
    FrozenId undefined0
  else
    let data = lazy begin
    let add_derivative_of evk evi acc =
      match advance sigma' evk with None -> acc | Some evk' -> Evar.Set.add evk' acc in
    let frozen = Evar.Map.fold add_derivative_of undefined0 Evar.Set.empty in
    let fold evk _ accu = if not (Evar.Set.mem evk frozen) then Evar.Set.add evk accu else accu in
    let pending = Evd.fold_undefined fold sigma' Evar.Set.empty in
    (frozen, pending)
    end in
    FrozenProgress data

let apply_typeclasses ~program_mode ~fail_evar env sigma frozen =
  let filter_frozen = match frozen with
    | FrozenId map -> fun evk -> Evar.Map.mem evk map
    | FrozenProgress (lazy (frozen, _)) -> fun evk -> Evar.Set.mem evk frozen
  in
  let sigma = Typeclasses.resolve_typeclasses
      ~filter:(if program_mode
               then (fun evk evi -> Typeclasses.no_goals_or_obligations evk evi && not (filter_frozen evk))
               else (fun evk evi -> Typeclasses.no_goals evk evi && not (filter_frozen evk)))
      ~split:true ~fail:fail_evar env sigma in
  let sigma = if program_mode then (* Try optionally solving the obligations *)
      Typeclasses.resolve_typeclasses
        ~filter:(fun evk evi -> Typeclasses.all_evars evk evi && not (filter_frozen evk)) ~split:true ~fail:false env sigma
    else sigma in
  sigma

let apply_inference_hook (hook : inference_hook) env sigma frozen = match frozen with
| FrozenId _ -> sigma
| FrozenProgress (lazy (_, pending)) ->
  Evar.Set.fold (fun evk sigma ->
    if Evd.is_undefined sigma evk (* in particular not defined by side-effect *)
    then
      match hook env sigma evk with
      | Some (sigma, c) ->
        Evd.define evk c sigma
      | None -> sigma
    else
      sigma) pending sigma

let apply_heuristics env sigma fail_evar =
  (* Resolve eagerly, potentially making wrong choices *)
  let flags = default_flags_of (Typeclasses.classes_transparent_state ()) in
  try solve_unif_constraints_with_heuristics ~flags env sigma
  with e when CErrors.noncritical e ->
    let e = Exninfo.capture e in
    if fail_evar then Exninfo.iraise e else sigma

let check_typeclasses_instances_are_solved ~program_mode env current_sigma frozen =
  (* Naive way, call resolution again with failure flag *)
  apply_typeclasses ~program_mode ~fail_evar:true env current_sigma frozen

let check_extra_evars_are_solved env current_sigma frozen = match frozen with
| FrozenId _ -> ()
| FrozenProgress (lazy (_, pending)) ->
  Evar.Set.iter
    (fun evk ->
      if not (Evd.is_defined current_sigma evk) then
        let (loc,k) = evar_source evk current_sigma in
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
         let (loc,k) = evar_source evk sigma in
         begin match k with
           | Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
           | _ -> Pretype_errors.error_unsolvable_implicit ?loc env sigma evk None
         end)
    | _ -> EConstr.iter sigma proc_rec c
  in proc_rec c

let check_evars_are_solved ~program_mode env sigma frozen =
  let sigma = check_typeclasses_instances_are_solved ~program_mode env sigma frozen in
  check_problems_are_solved env sigma;
  check_extra_evars_are_solved env sigma frozen

(* Try typeclasses, hooks, unification heuristics ... *)

let solve_remaining_evars ?hook flags env ?initial sigma =
  let program_mode = flags.program_mode in
  let frozen = frozen_and_pending_holes (initial, sigma) in
  let sigma =
    match flags.use_typeclasses with
    | UseTC -> apply_typeclasses ~program_mode ~fail_evar:false env sigma frozen
    | NoUseTC | UseTCForConv -> sigma
  in
  let sigma = match hook with
  | None -> sigma
  | Some hook -> apply_inference_hook hook env sigma frozen
  in
  let sigma = if flags.solve_unification_constraints
    then apply_heuristics env sigma false
    else sigma
  in
  if flags.fail_evar then check_evars_are_solved ~program_mode env sigma frozen;
  sigma

let check_evars_are_solved ~program_mode env ?initial current_sigma =
  let frozen = frozen_and_pending_holes (initial, current_sigma) in
  check_evars_are_solved ~program_mode env current_sigma frozen

let process_inference_flags flags env initial (sigma,c,cty) =
  let sigma = solve_remaining_evars flags env ~initial sigma in
  let c = if flags.expand_evars then nf_evar sigma c else c in
  sigma,c,cty

let adjust_evar_source sigma na c =
  match na, kind sigma c with
  | Name id, Evar (evk,args) ->
     let evi = Evd.find sigma evk in
     begin match evi.evar_source with
     | loc, Evar_kinds.QuestionMark {
         Evar_kinds.qm_obligation=b;
         Evar_kinds.qm_name=Anonymous;
         Evar_kinds.qm_record_field=recfieldname;
        } ->
        let src = (loc,Evar_kinds.QuestionMark {
            Evar_kinds.qm_obligation=b;
            Evar_kinds.qm_name=na;
            Evar_kinds.qm_record_field=recfieldname;
        }) in
        let (sigma, evk') = restrict_evar sigma evk (evar_filter evi) ~src None in
        sigma, mkEvar (evk',args)
     | _ -> sigma, c
     end
  | _, _ -> sigma, c

(* coerce to tycon if any *)
let inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma j = function
  | None -> sigma, j, Some Coercion.empty_coercion_trace
  | Some t ->
    Coercion.inh_conv_coerce_to ?loc ~program_mode resolve_tc !!env sigma j t

let check_instance loc subst = function
  | [] -> ()
  | (id,_) :: _ ->
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

let interp_known_glob_level ?loc evd = function
  | GSProp -> Univ.Level.sprop
  | GProp -> Univ.Level.prop
  | GSet -> Univ.Level.set
  | GType qid ->
    try interp_known_universe_level_name evd qid
    with Not_found ->
      user_err ?loc ~hdr:"interp_known_level_info" (str "Undeclared universe " ++ Libnames.pr_qualid qid)

let interp_glob_level ?loc evd : glob_level -> _ = function
  | UAnonymous {rigid} -> new_univ_level_variable ?loc (if rigid then univ_rigid else univ_flexible) evd
  | UNamed s -> interp_sort_name ?loc evd s

let interp_instance ?loc evd l =
  let evd, l' =
    List.fold_left
      (fun (evd, univs) l ->
         let evd, l = interp_glob_level ?loc evd l in
         (evd, l :: univs)) (evd, [])
      l
  in
  if List.exists (fun l -> Univ.Level.is_prop l) l' then
    user_err ?loc ~hdr:"pretype"
      (str "Universe instances cannot contain Prop, polymorphic" ++
       str " universe instances must be greater or equal to Set.");
  evd, Some (Univ.Instance.of_array (Array.of_list (List.rev l')))

let pretype_global ?loc rigid env evd gr us =
  let evd, instance =
    match us with
    | None -> evd, None
    | Some l -> interp_instance ?loc evd l
  in
  Evd.fresh_global ?loc ~rigid ?names:instance !!env evd gr

let pretype_ref ?loc sigma env ref us =
  match ref with
  | GlobRef.VarRef id ->
      (* Section variable *)
    (try
       let ty = NamedDecl.get_type (lookup_named id !!env) in
       (match us with
        | None | Some [] -> ()
        | Some (_ :: _) ->
          CErrors.user_err ?loc
            Pp.(str "Section variables are not polymorphic:" ++ spc ()
                ++ str "universe instance should have length 0."));
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

let interp_sort ?loc evd : glob_sort -> _ = function
  | UAnonymous {rigid} ->
    let evd, l = new_univ_level_variable ?loc (if rigid then univ_rigid else univ_flexible) evd in
    evd, Univ.Universe.make l
  | UNamed l -> interp_sort_info ?loc evd l

let judge_of_sort ?loc evd s =
  let judge =
    { uj_val = mkType s; uj_type = mkType (Univ.super s) }
  in
    evd, judge

let pretype_sort ?loc sigma s =
  match s with
  | UNamed [GSProp,0] -> sigma, judge_of_sprop
  | UNamed [GProp,0] -> sigma, judge_of_prop
  | UNamed [GSet,0] -> sigma, judge_of_set
  | _ ->
  let sigma, s = interp_sort ?loc sigma s in
  judge_of_sort ?loc sigma s

let new_type_evar env sigma loc =
  new_type_evar env sigma ~src:(Loc.tag ?loc Evar_kinds.InternalHole)

let mark_obligation_evar sigma k evc =
  match k with
  | Evar_kinds.QuestionMark _
  | Evar_kinds.ImplicitArg (_, _, false) ->
    Evd.set_obligation_evar sigma (fst (destEvar sigma evc))
  | _ -> sigma

type 'a pretype_fun = ?loc:Loc.t -> program_mode:bool -> poly:bool -> bool -> type_constraint -> GlobEnv.t -> evar_map -> evar_map * 'a

type pretyper = {
  pretype_ref : pretyper -> GlobRef.t * glob_level list option -> unsafe_judgment pretype_fun;
  pretype_var : pretyper -> Id.t -> unsafe_judgment pretype_fun;
  pretype_evar : pretyper -> existential_name * (Id.t * glob_constr) list -> unsafe_judgment pretype_fun;
  pretype_patvar : pretyper -> Evar_kinds.matching_var_kind -> unsafe_judgment pretype_fun;
  pretype_app : pretyper -> glob_constr * glob_constr list -> unsafe_judgment pretype_fun;
  pretype_lambda : pretyper -> Name.t * binding_kind * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_prod : pretyper -> Name.t * binding_kind * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_letin : pretyper -> Name.t * glob_constr * glob_constr option * glob_constr -> unsafe_judgment pretype_fun;
  pretype_cases : pretyper -> Constr.case_style * glob_constr option * tomatch_tuples * cases_clauses -> unsafe_judgment pretype_fun;
  pretype_lettuple : pretyper -> Name.t list * (Name.t * glob_constr option) * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_if : pretyper -> glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_rec : pretyper -> glob_fix_kind * Id.t array * glob_decl list array * glob_constr array * glob_constr array -> unsafe_judgment pretype_fun;
  pretype_sort : pretyper -> glob_sort -> unsafe_judgment pretype_fun;
  pretype_hole : pretyper -> Evar_kinds.t * Namegen.intro_pattern_naming_expr * Genarg.glob_generic_argument option -> unsafe_judgment pretype_fun;
  pretype_cast : pretyper -> glob_constr * glob_constr cast_type -> unsafe_judgment pretype_fun;
  pretype_int : pretyper -> Uint63.t -> unsafe_judgment pretype_fun;
  pretype_float : pretyper -> Float64.t -> unsafe_judgment pretype_fun;
  pretype_type : pretyper -> glob_constr -> unsafe_type_judgment pretype_fun;
}

(** Tie the loop *)
let eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma t =
  let loc = t.CAst.loc in
  match DAst.get t with
  | GRef (ref,u) ->
    self.pretype_ref self (ref, u) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GVar id ->
    self.pretype_var self id ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GEvar (evk, args) ->
    self.pretype_evar self (evk, args) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GPatVar knd ->
    self.pretype_patvar self knd ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GApp (c, args) ->
    self.pretype_app self (c, args) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GLambda (na, bk, t, c) ->
    self.pretype_lambda self (na, bk, t, c) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GProd (na, bk, t, c) ->
    self.pretype_prod self (na, bk, t, c) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GLetIn (na, b, t, c) ->
    self.pretype_letin self (na, b, t, c) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GCases (st, c, tm, cl) ->
    self.pretype_cases self (st, c, tm, cl) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GLetTuple (na, b, t, c) ->
    self.pretype_lettuple self (na, b, t, c) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GIf (c, r, t1, t2) ->
    self.pretype_if self (c, r, t1, t2) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GRec (knd, nas, decl, c, t) ->
    self.pretype_rec self (knd, nas, decl, c, t) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GSort s ->
    self.pretype_sort self s ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GHole (knd, nam, arg) ->
    self.pretype_hole self (knd, nam, arg) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GCast (c, t) ->
    self.pretype_cast self (c, t) ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GInt n ->
    self.pretype_int self n ?loc ~program_mode ~poly resolve_tc tycon env sigma
  | GFloat f ->
    self.pretype_float self f ?loc ~program_mode ~poly resolve_tc tycon env sigma

let eval_type_pretyper self ~program_mode ~poly resolve_tc tycon env sigma t =
  self.pretype_type self t ~program_mode ~poly resolve_tc tycon env sigma

let pretype_instance self ~program_mode ~poly resolve_tc env sigma loc hyps evk update =
  let f decl (subst,update,sigma) =
    let id = NamedDecl.get_id decl in
    let b = Option.map (replace_vars subst) (NamedDecl.get_value decl) in
    let t = replace_vars subst (NamedDecl.get_type decl) in
    let check_body sigma id c =
      match b, c with
      | Some b, Some c ->
         if not (is_conv !!env sigma b c) then
           user_err ?loc  (str "Cannot interpret " ++
             pr_existential_key sigma evk ++
             strbrk " in current context: binding for " ++ Id.print id ++
             strbrk " is not convertible to its expected definition (cannot unify " ++
             quote (Termops.Internal.print_constr_env !!env sigma b) ++
             strbrk " and " ++
             quote (Termops.Internal.print_constr_env !!env sigma c) ++
             str ").")
      | Some b, None ->
           user_err ?loc  (str "Cannot interpret " ++
             pr_existential_key sigma evk ++
             strbrk " in current context: " ++ Id.print id ++
             strbrk " should be bound to a local definition.")
      | None, _ -> () in
    let check_type sigma id t' =
      if not (is_conv !!env sigma t t') then
        user_err ?loc  (str "Cannot interpret " ++
          pr_existential_key sigma evk ++
          strbrk " in current context: binding for " ++ Id.print id ++
          strbrk " is not well-typed.") in
    let sigma, c, update =
      try
        let c = List.assoc id update in
        let sigma, c = eval_pretyper self ~program_mode ~poly resolve_tc (mk_tycon t) env sigma c in
        check_body sigma id (Some c.uj_val);
        sigma, c.uj_val, List.remove_assoc id update
      with Not_found ->
      try
        let (n,b',t') = lookup_rel_id id (rel_context !!env) in
        check_type sigma id (lift n t');
        check_body sigma id (Option.map (lift n) b');
        sigma, mkRel n, update
      with Not_found ->
      try
        let decl = lookup_named id !!env in
        check_type sigma id (NamedDecl.get_type decl);
        check_body sigma id (NamedDecl.get_value decl);
        sigma, mkVar id, update
      with Not_found ->
        user_err ?loc  (str "Cannot interpret " ++
          pr_existential_key sigma evk ++
          str " in current context: no binding for " ++ Id.print id ++ str ".") in
    ((id,c)::subst, update, sigma) in
  let subst,inst,sigma = List.fold_right f hyps ([],update,sigma) in
  check_instance loc subst inst;
  sigma, List.map snd subst

module Default =
struct

  let discard_trace (sigma,t,otrace) = sigma, t

  let pretype_ref self (ref, u) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let sigma, t_ref = pretype_ref ?loc sigma env ref u in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma t_ref tycon

  let pretype_var self id =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let pretype tycon env sigma t = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma t in
    let sigma, t_id = pretype_id (fun e r t -> pretype tycon e r t) loc env sigma id in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma t_id tycon

  let pretype_evar self (id, inst) ?loc ~program_mode ~poly resolve_tc tycon env sigma =
      (* Ne faudrait-il pas s'assurer que hyps est bien un
         sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
      let id = interp_ltac_id env id in
      let evk =
        try Evd.evar_key id sigma
        with Not_found -> error_evar_not_found ?loc !!env sigma id in
      let hyps = evar_filtered_context (Evd.find sigma evk) in
      let sigma, args = pretype_instance self ~program_mode ~poly resolve_tc env sigma loc hyps evk inst in
      let c = mkEvar (evk, args) in
      let j = Retyping.get_judgment_of !!env sigma c in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma j tycon

  let pretype_patvar self kind ?loc ~program_mode ~poly resolve_tc tycon env sigma =
    let sigma, ty =
      match tycon with
      | Some ty -> sigma, ty
      | None -> new_type_evar env sigma loc in
    let k = Evar_kinds.MatchingVar kind in
    let sigma, uj_val = new_evar env sigma ~src:(loc,k) ty in
    sigma, { uj_val; uj_type = ty }

  let pretype_hole self (k, naming, ext) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    match ext with
    | None ->
      let open Namegen in
      let naming = match naming with
        | IntroIdentifier id -> IntroIdentifier (interp_ltac_id env id)
        | IntroAnonymous -> IntroAnonymous
        | IntroFresh id -> IntroFresh (interp_ltac_id env id) in
      let sigma, ty =
        match tycon with
        | Some ty -> sigma, ty
        | None -> new_type_evar env sigma loc in
      let sigma, uj_val = new_evar env sigma ~src:(loc,k) ~naming ty in
      let sigma = if program_mode then mark_obligation_evar sigma k uj_val else sigma in
      sigma, { uj_val; uj_type = ty }

    | Some arg ->
      let sigma, ty =
        match tycon with
        | Some ty -> sigma, ty
        | None -> new_type_evar env sigma loc in
      let c, sigma = GlobEnv.interp_glob_genarg env poly sigma ty arg in
      sigma, { uj_val = c; uj_type = ty }

  let pretype_rec self (fixkind, names, bl, lar, vdef) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let hypnaming = if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames in
    let rec type_bl env sigma ctxt = function
      | [] -> sigma, ctxt
      | (na,bk,None,ty)::bl ->
        let sigma, ty' = pretype_type empty_valcon env sigma ty in
        let rty' = Sorts.relevance_of_sort ty'.utj_type in
        let dcl = LocalAssum (make_annot na rty', ty'.utj_val) in
        let dcl', env = push_rel ~hypnaming sigma dcl env in
        type_bl env sigma (Context.Rel.add dcl' ctxt) bl
      | (na,bk,Some bd,ty)::bl ->
        let sigma, ty' = pretype_type empty_valcon env sigma ty in
        let rty' = Sorts.relevance_of_sort ty'.utj_type in
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
             decompose_prod_n_assum sigma (Context.Rel.length ctxt)
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
          let possible_indexes =
            Array.to_list (Array.mapi
                             (fun i annot -> match annot with
                             | Some n -> [n]
                             | None -> List.map_i (fun i _ -> i) 0 ctxtv.(i))
           vn)
          in
          let fixdecls = (names,ftys,fdefs) in
          let indexes = esearch_guard ?loc !!env sigma possible_indexes fixdecls in
          make_judge (mkFixOpt ((indexes,i),fixdecls)) ftys.(i)
        | GCoFix i ->
          let fixdecls = (names,ftys,fdefs) in
          let cofix = (i, fixdecls) in
            (try check_cofix !!env (i, nf_fix sigma fixdecls)
             with reraise ->
               let (e, info) = Exninfo.capture reraise in
               let info = Option.cata (Loc.add_loc info) info loc in
               Exninfo.iraise (e, info));
            make_judge (mkCoFix cofix) ftys.(i)
      in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma fixj tycon

  let pretype_sort self s =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let sigma, j = pretype_sort ?loc sigma s in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma j tycon

  let pretype_app self (f, args) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
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
          Option.default length @@ GlobRef.Map.find_opt gr !bidi_hints
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
      if program_mode && length > 0 && isConstruct sigma fj.uj_val then
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
              if eq_ind ind ind' then List.map EConstr.of_constr pars
              else (* Let the usual code throw an error *) []
            with Not_found -> []
      else []
    in
    let app_f =
      match EConstr.kind sigma fj.uj_val with
      | Const (p, u) when Recordops.is_primitive_projection p ->
        let p = Option.get @@ Recordops.find_primitive_projection p in
        let p = Projection.make p false in
        let npars = Projection.npars p in
        fun n ->
          if Int.equal n npars then fun _ v -> mkProj (p, v)
          else fun f v -> applist (f, [v])
      | _ -> fun _ f v -> applist (f, [v])
    in
    let refresh_template env sigma resj =
      (* Special case for inductive type applications that must be
         refreshed right away. *)
      match EConstr.kind sigma resj.uj_val with
      | App (f,args) ->
        if Termops.is_template_polymorphic_ind !!env sigma f then
          let c = mkApp (f, args) in
          let sigma, c = Evarsolve.refresh_universes (Some true) !!env sigma c in
          let t = Retyping.get_type_of !!env sigma c in
          sigma, make_judge c (* use this for keeping evars: resj.uj_val *) t
        else sigma, resj
      | _ -> sigma, resj
    in
    let rec apply_rec env sigma n resj resj_before_bidi candargs bidiargs = function
      | [] -> sigma, resj, resj_before_bidi, List.rev bidiargs
      | c::rest ->
        let bidi = n >= nargs_before_bidi in
        let argloc = loc_of_glob_constr c in
        let sigma, resj, trace = Coercion.inh_app_fun ~program_mode resolve_tc !!env sigma resj in
        let resty = whd_all !!env sigma resj.uj_type in
        match EConstr.kind sigma resty with
        | Prod (na,c1,c2) ->
          let (sigma, hj), bidiargs =
            if bidi then
              (* We want to get some typing information from the context before
              typing the argument, so we replace it by an existential
              variable *)
              let sigma, c_hole = new_evar env sigma ~src:(loc,Evar_kinds.InternalHole) c1 in
              (sigma, make_judge c_hole c1), (c_hole, c, trace) :: bidiargs
            else
              let tycon = Some c1 in
              pretype tycon env sigma c, bidiargs
          in
          let sigma, candargs, ujval =
            match candargs with
            | [] -> sigma, [], j_val hj
            | arg :: args ->
              begin match Evarconv.unify_delay !!env sigma (j_val hj) arg with
                | exception Evarconv.UnableToUnify _ ->
                  sigma, [], j_val hj
                | sigma ->
                  sigma, args, nf_evar sigma (j_val hj)
              end
          in
          let sigma, ujval = adjust_evar_source sigma na.binder_name ujval in
          let value, typ = app_f n (j_val resj) ujval, subst1 ujval c2 in
          let resj = { uj_val = value; uj_type = typ } in
          let resj_before_bidi = if bidi then resj_before_bidi else resj in
          apply_rec env sigma (n+1) resj resj_before_bidi candargs bidiargs rest
        | _ ->
          let sigma, hj = pretype empty_tycon env sigma c in
          error_cant_apply_not_functional
            ?loc:(Loc.merge_opt floc argloc) !!env sigma resj [|hj|]
    in
    let sigma, resj, resj_before_bidi, bidiargs = apply_rec env sigma 0 fj fj candargs [] args in
    let sigma, resj = refresh_template env sigma resj in
    let sigma, resj, otrace = inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma resj tycon in
    let refine_arg n (sigma,t) (newarg,origarg,trace) =
      (* Refine an argument (originally `origarg`) represented by an evar
         (`newarg`) to use typing information from the context *)
      (* Recover the expected type of the argument *)
      let ty = Retyping.get_type_of !!env sigma newarg in
      (* Type the argument using this expected type *)
      let sigma, j = pretype (Some ty) env sigma origarg in
      (* Unify the (possibly refined) existential variable with the
      (typechecked) original value *)
      let sigma = Evarconv.unify_delay !!env sigma newarg (j_val j) in
      sigma, app_f n (Coercion.reapply_coercions sigma trace t) (j_val j)
    in
    (* We now refine any arguments whose typing was delayed for
       bidirectionality *)
    let t = resj_before_bidi.uj_val in
    let sigma, t = List.fold_left_i refine_arg nargs_before_bidi (sigma,t) bidiargs in
    (* If we did not get a coercion trace (e.g. with `Program` coercions, we
    replaced user-provided arguments with inferred ones. Otherwise, we apply
    the coercion trace to the user-provided arguments. *)
    let resj =
      match otrace with
      | None -> resj
      | Some trace ->
        let resj = { resj with uj_val = t } in
        let sigma, resj = refresh_template env sigma resj in
        { resj with uj_val = Coercion.reapply_coercions sigma trace t }
    in
    (sigma, resj)

  let pretype_lambda self (name, bk, c1, c2) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let open Context.Rel.Declaration in
    let sigma, tycon' =
      match tycon with
      | None -> sigma, tycon
      | Some ty ->
        let sigma, ty' = Coercion.inh_coerce_to_prod ?loc ~program_mode !!env sigma ty in
        sigma, Some ty'
    in
    let sigma, (name',dom,rng) = split_tycon ?loc !!env sigma tycon' in
    let dom_valcon = valcon_of_tycon dom in
    let sigma, j = eval_type_pretyper self ~program_mode ~poly resolve_tc dom_valcon env sigma c1 in
    let name = {binder_name=name; binder_relevance=Sorts.relevance_of_sort j.utj_type} in
    let var = LocalAssum (name, j.utj_val) in
    let hypnaming = if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames in
    let var',env' = push_rel ~hypnaming sigma var env in
    let sigma, j' = eval_pretyper self ~program_mode ~poly resolve_tc rng env' sigma c2 in
    let name = get_name var' in
    let resj = judge_of_abstraction !!env (orelse_name name name'.binder_name) j j' in
    discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma resj tycon

  let pretype_prod self (name, bk, c1, c2) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let sigma, j = pretype_type empty_valcon env sigma c1 in
    let hypnaming = if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames in
    let sigma, name, j' = match name with
      | Anonymous ->
        let sigma, j = pretype_type empty_valcon env sigma c2 in
        sigma, name, { j with utj_val = lift 1 j.utj_val }
      | Name _ ->
        let r = Sorts.relevance_of_sort j.utj_type in
        let var = LocalAssum (make_annot name r, j.utj_val) in
        let var, env' = push_rel ~hypnaming sigma var env in
        let sigma, c2_j = pretype_type empty_valcon env' sigma c2 in
        sigma, get_name var, c2_j
    in
    let resj =
      try
        judge_of_product !!env name j j'
      with TypeError _ as e ->
        let (e, info) = Exninfo.capture e in
        let info = Option.cata (Loc.add_loc info) info loc in
        Exninfo.iraise (e, info) in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma resj tycon

  let pretype_letin self (name, c1, t, c2) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
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
    let hypnaming = if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames in
    let var, env = push_rel ~hypnaming sigma var env in
    let sigma, j' = pretype tycon env sigma c2 in
    let name = get_name var in
    sigma, { uj_val = mkLetIn (make_annot name r, j.uj_val, t, j'.uj_val) ;
             uj_type = subst1 j.uj_val j'.uj_type }

  let pretype_lettuple self (nal, (na, po), c, d) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let pretype_type tycon env sigma c = eval_type_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let sigma, cj = pretype empty_tycon env sigma c in
    let (IndType (indf,realargs)) =
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
      let set_name na d = set_name na (map_rel_decl EConstr.of_constr d) in
      match Environ.get_projections !!env ind with
      | None ->
         List.map2 set_name (List.rev nal) cs.cs_args, false
      | Some ps ->
        let rec aux n k names l =
          match names, l with
          | na :: names, (LocalAssum (na', t) :: l) ->
            let t = EConstr.of_constr t in
            let proj = Projection.make ps.(cs.cs_nargs - k) true in
            LocalDef ({na' with binder_name = na},
                      lift (cs.cs_nargs - n) (mkProj (proj, cj.uj_val)), t)
            :: aux (n+1) (k + 1) names l
          | na :: names, (decl :: l) ->
            set_name na decl :: aux (n+1) k names l
          | [], [] -> []
          | _ -> assert false
        in aux 1 1 (List.rev nal) cs.cs_args, true in
    let fsign = Context.Rel.map (whd_betaiota !!env sigma) fsign in
    let hypnaming = if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames in
    let fsign,env_f = push_rel_context ~hypnaming sigma fsign env in
    let obj ind rci p v f =
      if not record then
        let f = it_mkLambda_or_LetIn f fsign in
        let ci = make_case_info !!env (fst ind) rci LetStyle in
          mkCase (ci, p, cj.uj_val,[|f|])
      else it_mkLambda_or_LetIn f fsign
    in
    (* Make dependencies from arity signature impossible *)
    let arsgn, indr =
      let arsgn,s = get_arity !!env indf in
      List.map (set_name Anonymous) arsgn, Sorts.relevance_of_sort_family s
    in
      let indt = build_dependent_inductive !!env indf in
      let psign = LocalAssum (make_annot na indr, indt) :: arsgn in (* For locating names in [po] *)
      let psign = List.map (fun d -> map_rel_decl EConstr.of_constr d) psign in
      let predenv = Cases.make_return_predicate_ltac_lvar env sigma na c cj.uj_val in
      let nar = List.length arsgn in
      let psign',env_p = push_rel_context ~hypnaming ~force_names:true sigma psign predenv in
          (match po with
          | Some p ->
            let sigma, pj = pretype_type empty_valcon env_p sigma p in
            let ccl = nf_evar sigma pj.utj_val in
            let p = it_mkLambda_or_LetIn ccl psign' in
            let inst =
              (Array.map_to_list EConstr.of_constr cs.cs_concl_realargs)
              @[EConstr.of_constr (build_dependent_constructor cs)] in
            let lp = lift cs.cs_nargs p in
            let fty = hnf_lam_applist !!env sigma lp inst in
            let sigma, fj = pretype (mk_tycon fty) env_f sigma d in
            let v =
              let ind,_ = dest_ind_family indf in
                let rci = Typing.check_allowed_sort !!env sigma ind cj.uj_val p in
                obj ind rci p cj.uj_val fj.uj_val
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
            let v =
              let ind,_ = dest_ind_family indf in
                let rci = Typing.check_allowed_sort !!env sigma ind cj.uj_val p in
                obj ind rci p cj.uj_val fj.uj_val
            in sigma, { uj_val = v; uj_type = ccl })

  let pretype_cases self (sty, po, tml, eqns)  =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    Cases.compile_cases ?loc ~program_mode sty (pretype, sigma) tycon env (po,tml,eqns)

  let pretype_if self (c, (na, po), b1, b2) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let open Context.Rel.Declaration in
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let sigma, cj = pretype empty_tycon env sigma c in
    let (IndType (indf,realargs)) =
      try find_rectype !!env sigma cj.uj_type
      with Not_found ->
        let cloc = loc_of_glob_constr c in
          error_case_not_inductive ?loc:cloc !!env sigma cj in
    let cstrs = get_constructors !!env indf in
      if not (Int.equal (Array.length cstrs) 2) then
        user_err ?loc
                      (str "If is only for inductive types with two constructors.");

      let arsgn, indr =
        let arsgn,s = get_arity !!env indf in
        (* Make dependencies from arity signature impossible *)
        List.map (set_name Anonymous) arsgn, Sorts.relevance_of_sort_family s
      in
      let nar = List.length arsgn in
      let indt = build_dependent_inductive !!env indf in
      let psign = LocalAssum (make_annot na indr, indt) :: arsgn in (* For locating names in [po] *)
      let psign = List.map (fun d -> map_rel_decl EConstr.of_constr d) psign in
      let predenv = Cases.make_return_predicate_ltac_lvar env sigma na c cj.uj_val in
    let hypnaming = if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames in
      let psign,env_p = push_rel_context ~hypnaming sigma psign predenv in
      let sigma, pred, p = match po with
        | Some p ->
          let sigma, pj = eval_type_pretyper self ~program_mode ~poly resolve_tc empty_valcon env_p sigma p in
          let ccl = nf_evar sigma pj.utj_val in
          let pred = it_mkLambda_or_LetIn ccl psign in
          let typ = lift (- nar) (beta_applist sigma (pred,[cj.uj_val])) in
          sigma, pred, typ
        | None ->
          let sigma, p = match tycon with
            | Some ty -> sigma, ty
            | None -> new_type_evar env sigma loc
          in
          sigma, it_mkLambda_or_LetIn (lift (nar+1) p) psign, p in
      let pred = nf_evar sigma pred in
      let p = nf_evar sigma p in
      let f sigma cs b =
        let n = Context.Rel.length cs.cs_args in
        let pi = lift n pred in (* liftn n 2 pred ? *)
        let pi = beta_applist sigma (pi, [EConstr.of_constr (build_dependent_constructor cs)]) in
        let cs_args = List.map (fun d -> map_rel_decl EConstr.of_constr d) cs.cs_args in
        let cs_args = Context.Rel.map (whd_betaiota !!env sigma) cs_args in
        let csgn =
          List.map (set_name Anonymous) cs_args
        in
        let _,env_c = push_rel_context ~hypnaming sigma csgn env in
        let sigma, bj = pretype (mk_tycon pi) env_c sigma b in
        sigma, it_mkLambda_or_LetIn bj.uj_val cs_args in
      let sigma, b1 = f sigma cstrs.(0) b1 in
      let sigma, b2 = f sigma cstrs.(1) b2 in
      let v =
        let ind,_ = dest_ind_family indf in
        let pred = nf_evar sigma pred in
        let rci = Typing.check_allowed_sort !!env sigma ind cj.uj_val pred in
        let ci = make_case_info !!env (fst ind) rci IfStyle in
          mkCase (ci, pred, cj.uj_val, [|b1;b2|])
      in
      let cj = { uj_val = v; uj_type = p } in
      discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma cj tycon

  let pretype_cast self (c, k) =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
    let pretype tycon env sigma c = eval_pretyper self ~program_mode ~poly resolve_tc tycon env sigma c in
    let sigma, cj =
      match k with
      | CastCoerce ->
        let sigma, cj = pretype empty_tycon env sigma c in
        Coercion.inh_coerce_to_base ?loc ~program_mode !!env sigma cj
      | CastConv t | CastVM t | CastNative t ->
        let k = (match k with CastVM _ -> VMcast | CastNative _ -> NATIVEcast | _ -> DEFAULTcast) in
        let sigma, tj = eval_type_pretyper self ~program_mode ~poly resolve_tc empty_valcon env sigma t in
        let sigma, tval = Evarsolve.refresh_universes
            ~onlyalg:true ~status:Evd.univ_flexible (Some false) !!env sigma tj.utj_val in
        let tval = nf_evar sigma tval in
        let (sigma, cj), tval = match k with
          | VMcast ->
            let sigma, cj = pretype empty_tycon env sigma c in
            let cty = nf_evar sigma cj.uj_type and tval = nf_evar sigma tval in
              if not (occur_existential sigma cty || occur_existential sigma tval) then
                match Reductionops.vm_infer_conv !!env sigma cty tval with
                | Some sigma -> (sigma, cj), tval
                | None ->
                  error_actual_type ?loc !!env sigma cj tval
                      (ConversionFailed (!!env,cty,tval))
              else user_err ?loc  (str "Cannot check cast with vm: " ++
                str "unresolved arguments remain.")
          | NATIVEcast ->
            let sigma, cj = pretype empty_tycon env sigma c in
            let cty = nf_evar sigma cj.uj_type and tval = nf_evar sigma tval in
            begin
              match Nativenorm.native_infer_conv !!env sigma cty tval with
              | Some sigma -> (sigma, cj), tval
              | None ->
                error_actual_type ?loc !!env sigma cj tval
                  (ConversionFailed (!!env,cty,tval))
            end
          | _ ->
            pretype (mk_tycon tval) env sigma c, tval
        in
        let v = mkCast (cj.uj_val, k, tval) in
        sigma, { uj_val = v; uj_type = tval }
    in discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma cj tycon

  let pretype_int self i =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
        let resj =
          try Typing.judge_of_int !!env i
          with Invalid_argument _ ->
            user_err ?loc ~hdr:"pretype" (str "Type of int63 should be registered first.")
        in
        discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma resj tycon

  let pretype_float self f =
    fun ?loc ~program_mode ~poly resolve_tc tycon env sigma ->
      let resj =
        try Typing.judge_of_float !!env f
        with Invalid_argument _ ->
          user_err ?loc ~hdr:"pretype" (str "Type of float should be registered first.")
        in
        discard_trace @@ inh_conv_coerce_to_tycon ?loc ~program_mode resolve_tc env sigma resj tycon

(* [pretype_type valcon env sigma c] coerces [c] into a type *)
let pretype_type self c ?loc ~program_mode ~poly resolve_tc valcon (env : GlobEnv.t) sigma = match DAst.get c with
  | GHole (knd, naming, None) ->
      let loc = loc_of_glob_constr c in
      (match valcon with
       | Some v ->
           let sigma, s =
             let t = Retyping.get_type_of !!env sigma v in
               match EConstr.kind sigma (whd_all !!env sigma t) with
               | Sort s ->
                 sigma, ESorts.kind sigma s
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
         let sigma = if program_mode then mark_obligation_evar sigma knd utj_val else sigma in
         sigma, { utj_val; utj_type = s})
  | _ ->
      let sigma, j = eval_pretyper self ~program_mode ~poly resolve_tc empty_tycon env sigma c in
      let loc = loc_of_glob_constr c in
      let sigma, tj = Coercion.inh_coerce_to_sort ?loc !!env sigma j in
        match valcon with
        | None -> sigma, tj
        | Some v ->
          begin match Evarconv.unify_leq_delay !!env sigma v tj.utj_val with
            | sigma -> sigma, tj
            | exception Evarconv.UnableToUnify _ ->
              error_unexpected_type
                ?loc:(loc_of_glob_constr c) !!env sigma tj.utj_val v
          end

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
    pretype_lambda = pretype_lambda;
    pretype_prod = pretype_prod;
    pretype_letin = pretype_letin;
    pretype_cases = pretype_cases;
    pretype_lettuple = pretype_lettuple;
    pretype_if = pretype_if;
    pretype_rec = pretype_rec;
    pretype_sort = pretype_sort;
    pretype_hole = pretype_hole;
    pretype_cast = pretype_cast;
    pretype_int = pretype_int;
    pretype_float = pretype_float;
    pretype_type = pretype_type;
  }

let pretype ~program_mode ~poly resolve_tc tycon env sigma c =
  eval_pretyper default_pretyper ~program_mode ~poly resolve_tc tycon env sigma c

let pretype_type ~program_mode ~poly resolve_tc tycon env sigma c =
  eval_type_pretyper default_pretyper ~program_mode ~poly resolve_tc tycon env sigma c

let ise_pretype_gen flags env sigma lvar kind c =
  let program_mode = flags.program_mode in
  let poly = flags.polymorphic in
  let hypnaming =
    if program_mode then ProgramNaming else KeepUserNameAndRenameExistingButSectionNames
  in
  let env = GlobEnv.make ~hypnaming env sigma lvar in
  let use_tc = match flags.use_typeclasses with
    | NoUseTC -> false
    | UseTC | UseTCForConv -> true
  in
  let sigma', c', c'_ty = match kind with
    | WithoutTypeConstraint | UnknownIfTermOrType ->
      let sigma, j = pretype ~program_mode ~poly use_tc empty_tycon env sigma c in
      sigma, j.uj_val, j.uj_type
    | OfType exptyp ->
      let sigma, j = pretype ~program_mode ~poly use_tc (mk_tycon exptyp) env sigma c in
      sigma, j.uj_val, j.uj_type
    | IsType ->
      let sigma, tj = pretype_type ~program_mode ~poly use_tc empty_valcon env sigma c in
      sigma, tj.utj_val, mkSort tj.utj_type
  in
  process_inference_flags flags !!env sigma (sigma',c',c'_ty)

let default_inference_flags fail = {
  use_typeclasses = UseTC;
  solve_unification_constraints = true;
  fail_evar = fail;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
}

let no_classes_no_fail_inference_flags = {
  use_typeclasses = NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
}

let all_and_fail_flags = default_inference_flags true
let all_no_fail_flags = default_inference_flags false

let ise_pretype_gen_ctx flags env sigma lvar kind c =
  let sigma, c, _ = ise_pretype_gen flags env sigma lvar kind c in
  c, Evd.evar_universe_context sigma

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

let path_convertible env sigma i p q =
  let open Coercionops in
  let mkGRef ref          = DAst.make @@ Glob_term.GRef(ref,None) in
  let mkGVar id           = DAst.make @@ Glob_term.GVar(id) in
  let mkGApp(rt,rtl)      = DAst.make @@ Glob_term.GApp(rt,rtl) in
  let mkGLambda(n,t,b)    = DAst.make @@ Glob_term.GLambda(n,Explicit,t,b) in
  let mkGSort u           = DAst.make @@ Glob_term.GSort u in
  let mkGHole ()          = DAst.make @@ Glob_term.GHole(Evar_kinds.BinderType Anonymous,Namegen.IntroAnonymous,None) in
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
      let cl,params = class_info_from_index i in
      let clty =
        match cl with
        | CL_SORT -> mkGSort (Glob_term.UAnonymous {rigid=false})
        | CL_FUN -> anomaly (str "A source class must not be Funclass.")
        | CL_SECVAR v -> mkGRef (GlobRef.VarRef v)
        | CL_CONST c -> mkGRef (GlobRef.ConstRef c)
        | CL_IND i -> mkGRef (GlobRef.IndRef i)
        | CL_PROJ p -> mkGRef (GlobRef.ConstRef (Projection.Repr.constant p))
      in
      let names =
        List.init params.cl_param
          (fun n -> Id.of_string ("x" ^ string_of_int n))
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

let _ = Coercionops.install_path_comparator path_convertible
