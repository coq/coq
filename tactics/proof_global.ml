(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Context

module NamedDecl = Context.Named.Declaration

(*** Proof Global Environment ***)

type proof_object =
  { name : Names.Id.t
  (* [name] only used in the STM *)
  ; entries : Evd.side_effects Declare.proof_entry list
  ; uctx: UState.t
  }

type opacity_flag = Opaque | Transparent

type t =
  { endline_tactic : Genarg.glob_generic_argument option
  ; section_vars : Id.Set.t option
  ; proof : Proof.t
  ; udecl: UState.universe_decl
  (** Initial universe declarations *)
  ; initial_euctx : UState.t
  (** The initial universe context (for the statement) *)
  }

(*** Proof Global manipulation ***)

let get_proof ps = ps.proof
let get_proof_name ps = (Proof.data ps.proof).Proof.name

let get_initial_euctx ps = ps.initial_euctx

let map_proof f p = { p with proof = f p.proof }
let map_fold_proof f p = let proof, res = f p.proof in { p with proof }, res

let map_fold_proof_endline f ps =
  let et =
    match ps.endline_tactic with
    | None -> Proofview.tclUNIT ()
    | Some tac ->
      let open Geninterp in
      let {Proof.poly} = Proof.data ps.proof in
      let ist = { lfun = Id.Map.empty; poly; extra = TacStore.empty } in
      let Genarg.GenArg (Genarg.Glbwit tag, tac) = tac in
      let tac = Geninterp.interp tag ist tac in
      Ftactic.run tac (fun _ -> Proofview.tclUNIT ())
  in
  let (newpr,ret) = f et ps.proof in
  let ps = { ps with proof = newpr } in
  ps, ret

let compact_the_proof pf = map_proof Proof.compact pf

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac ps =
  { ps with endline_tactic = Some tac }

(** [start_proof ~name ~udecl ~poly sigma goals] starts a proof of
   name [name] with goals [goals] (a list of pairs of environment and
   conclusion). The proof is started in the evar map [sigma] (which
   can typically contain universe constraints), and with universe
   bindings [udecl]. *)
let start_proof ~name ~udecl ~poly sigma goals =
  let proof = Proof.start ~name ~poly sigma goals in
  let initial_euctx = Evd.evar_universe_context Proof.((data proof).sigma) in
  { proof
  ; endline_tactic = None
  ; section_vars = None
  ; udecl
  ; initial_euctx
  }

let start_dependent_proof ~name ~udecl ~poly goals =
  let proof = Proof.dependent_start ~name ~poly goals in
  let initial_euctx = Evd.evar_universe_context Proof.((data proof).sigma) in
  { proof
  ; endline_tactic = None
  ; section_vars = None
  ; udecl
  ; initial_euctx
  }

let get_used_variables pf = pf.section_vars
let get_universe_decl pf = pf.udecl

let set_used_variables ps l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  let ctx_set =
    List.fold_right Id.Set.add (List.map NamedDecl.get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe as orig) =
    match entry with
    | LocalAssum ({binder_name=x},_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe)
    | LocalDef ({binder_name=x},bo, ty) as decl ->
       if Id.Set.mem x all_safe then orig else
       let vars = Id.Set.union (vars_of env bo) (vars_of env ty) in
       if Id.Set.subset vars all_safe
       then (decl :: ctx, Id.Set.add x all_safe)
       else (ctx, all_safe) in
  let ctx, _ =
    Environ.fold_named_context aux env ~init:(ctx,ctx_set) in
  if not (Option.is_empty ps.section_vars) then
    CErrors.user_err Pp.(str "Used section variables can be declared only once");
  ctx, { ps with section_vars = Some (Context.Named.to_vars ctx) }

let get_open_goals ps =
  let Proof.{ goals; stack; shelf } = Proof.data ps.proof in
  List.length goals +
  List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) stack) +
  List.length shelf

type closed_proof_output = (Constr.t * Evd.side_effects) list * UState.t

let private_poly_univs =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Private";"Polymorphic";"Universes"]
    ~value:true

(* XXX: This is still separate from close_proof below due to drop_pt in the STM *)
(* XXX: Unsafe_typ:true is needed by vio files, see bf0499bc507d5a39c3d5e3bf1f69191339270729 *)
let prepare_proof ~unsafe_typ { proof } =
  let Proof.{name=pid;entry;poly} = Proof.data proof in
  let initial_goals = Proofview.initial_goals entry in
  let evd = Proof.return ~pid proof in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  let to_constr_body c =
    match EConstr.to_constr_opt evd c with
    | Some p -> p
    | None -> CErrors.user_err Pp.(str "Some unresolved existential variables remain")
  in
  let to_constr_typ t =
    if unsafe_typ then EConstr.Unsafe.to_constr t else to_constr_body t
  in
  (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
  (* EJGA: actually side-effects de-duplication and this codepath is
     unrelated. Duplicated side-effects arise from incorrect scheme
     generation code, the main bulk of it was mostly fixed by #9836
     but duplication can still happen because of rewriting schemes I
     think; however the code below is mostly untested, the only
     code-paths that generate several proof entries are derive and
     equations and so far there is no code in the CI that will
     actually call those and do a side-effect, TTBOMK *)
  (* EJGA: likely the right solution is to attach side effects to the first constant only? *)
  let proofs = List.map (fun (body, typ) -> (to_constr_body body, eff), to_constr_typ typ) initial_goals in
  proofs, Evd.evar_universe_context evd

let close_proof ~opaque ~keep_body_ucst_separate ps =

  let { section_vars; proof; udecl; initial_euctx } = ps in
  let { Proof.name; poly } = Proof.data proof in
  let unsafe_typ = keep_body_ucst_separate && not poly in
  let elist, uctx = prepare_proof ~unsafe_typ ps in
  let opaque = match opaque with Opaque -> true | Transparent -> false in

  let make_entry ((body, eff), typ) =

    let allow_deferred =
      not poly &&
      (keep_body_ucst_separate
       || not (Safe_typing.is_empty_private_constants eff.Evd.seff_private))
    in
    let used_univs_body = Vars.universes_of_constr body in
    let used_univs_typ = Vars.universes_of_constr typ in
    let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
    let utyp, ubody =
      if allow_deferred then
        let utyp = UState.univ_entry ~poly initial_euctx in
        let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
        (* For vi2vo compilation proofs are computed now but we need to
           complement the univ constraints of the typ with the ones of
           the body.  So we keep the two sets distinct. *)
        let uctx_body = UState.restrict uctx used_univs in
        let ubody = UState.check_mono_univ_decl uctx_body udecl in
        utyp, ubody
      else if poly && opaque && private_poly_univs () then
        let universes = UState.restrict uctx used_univs in
        let typus = UState.restrict universes used_univs_typ in
        let utyp = UState.check_univ_decl ~poly typus udecl in
        let ubody = Univ.ContextSet.diff
            (UState.context_set universes)
            (UState.context_set typus)
        in
        utyp, ubody
      else
        (* Since the proof is computed now, we can simply have 1 set of
           constraints in which we merge the ones for the body and the ones
           for the typ. We recheck the declaration after restricting with
           the actually used universes.
           TODO: check if restrict is really necessary now. *)
        let ctx = UState.restrict uctx used_univs in
        let utyp = UState.check_univ_decl ~poly ctx udecl in
        utyp, Univ.ContextSet.empty
    in
    Declare.definition_entry ~opaque ?section_vars ~univs:utyp ~univsbody:ubody ~types:typ ~eff body
  in
  let entries = CList.map make_entry elist  in
  { name; entries; uctx }

let close_proof_delayed ~feedback_id ps (fpl : closed_proof_output Future.computation) =
  let { section_vars; proof; udecl; initial_euctx } = ps in
  let { Proof.name; poly; entry; sigma } = Proof.data proof in

  (* We don't allow poly = true in this path *)
  if poly then
    CErrors.anomaly (Pp.str "Cannot delay universe-polymorphic constants.");

  let fpl, uctx = Future.split2 fpl in
  (* Because of dependent subgoals at the beginning of proofs, we could
     have existential variables in the initial types of goals, we need to
     normalise them for the kernel. *)
  let subst_evar k = Evd.existential_opt_value0 sigma k in
  let nf = UnivSubst.nf_evars_and_universes_opt_subst subst_evar (UState.subst initial_euctx) in

  (* We only support opaque proofs, this will be enforced by using
     different entries soon *)
  let opaque = true in
  let make_entry p (_, types) =
    (* Already checked the univ_decl for the type universes when starting the proof. *)
    let univs = UState.univ_entry ~poly:false initial_euctx in
    let types = nf (EConstr.Unsafe.to_constr types) in

    Future.chain p (fun (pt,eff) ->
        (* Deferred proof, we already checked the universe declaration with
             the initial universes, ensure that the final universes respect
             the declaration as well. If the declaration is non-extensible,
             this will prevent the body from adding universes and constraints. *)
        let uctx = Future.force uctx in
        let uctx = UState.constrain_variables (fst (UState.context_set initial_euctx)) uctx in
        let used_univs = Univ.LSet.union
            (Vars.universes_of_constr types)
            (Vars.universes_of_constr pt)
        in
        let univs = UState.restrict uctx used_univs in
        let univs = UState.check_mono_univ_decl univs udecl in
        (pt,univs),eff)
    |> Declare.delayed_definition_entry ~opaque ~feedback_id ?section_vars ~univs ~types
  in
  let entries = Future.map2 make_entry fpl (Proofview.initial_goals entry) in
  { name; entries; uctx = initial_euctx }

let close_future_proof = close_proof_delayed

let return_partial_proof { proof } =
 let proofs = Proof.partial_proof proof in
 let Proof.{sigma=evd} = Proof.data proof in
 let eff = Evd.eval_side_effects evd in
 (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
 let proofs = List.map (fun c -> EConstr.Unsafe.to_constr c, eff) proofs in
 proofs, Evd.evar_universe_context evd

let return_proof ps =
  let p, uctx = prepare_proof ~unsafe_typ:false ps in
  List.map fst p, uctx

let update_global_env =
  map_proof (fun p ->
      let { Proof.sigma } = Proof.data p in
      let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
      let p, (status,info), _ = Proof.run_tactic (Global.env ()) tac p in
      p)

let next = let n = ref 0 in fun () -> incr n; !n

let by tac = map_fold_proof (Pfedit.solve (Goal_select.SelectNth 1) None tac)

let build_constant_by_tactic ~name ?(opaque=Transparent) ~uctx ~sign ~poly typ tac =
  let evd = Evd.from_ctx uctx in
  let goals = [ (Global.env_of_context sign , typ) ] in
  let pf = start_proof ~name ~poly ~udecl:UState.default_univ_decl evd goals in
  let pf, status = by tac pf in
  let { entries; uctx } = close_proof ~opaque ~keep_body_ucst_separate:false pf in
  match entries with
  | [entry] ->
    entry, status, uctx
  | _ ->
    CErrors.anomaly Pp.(str "[build_constant_by_tactic] close_proof returned more than one proof term")

let build_by_tactic ?(side_eff=true) env ~uctx ~poly ~typ tac =
  let name = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = Environ.(val_of_named_context (named_context env)) in
  let ce, status, univs = build_constant_by_tactic ~name ~uctx ~sign ~poly typ tac in
  let cb, uctx =
    if side_eff then Declare.inline_private_constants ~uctx env ce
    else
      (* GG: side effects won't get reset: no need to treat their universes specially *)
      let (cb, ctx), _eff = Future.force ce.Declare.proof_entry_body in
      cb, UState.merge ~sideff:false Evd.univ_rigid uctx ctx
  in
  cb, ce.Declare.proof_entry_type, status, univs

exception NoSuchGoal
let () = CErrors.register_handler begin function
  | NoSuchGoal -> Some Pp.(str "No such goal.")
  | _ -> None
end

let get_nth_V82_goal p i =
  let Proof.{ sigma; goals } = Proof.data p in
  try { Evd.it = List.nth goals (i-1) ; sigma }
  with Failure _ -> raise NoSuchGoal

let get_goal_context_gen pf i =
  let { Evd.it=goal ; sigma=sigma; } = get_nth_V82_goal pf i in
  (sigma, Refiner.pf_env { Evd.it=goal ; sigma=sigma; })

let get_goal_context pf i =
  let p = get_proof pf in
  get_goal_context_gen p i

let get_current_goal_context pf =
  let p = get_proof pf in
  try get_goal_context_gen p 1
  with
  | NoSuchGoal ->
    (* spiwack: returning empty evar_map, since if there is no goal,
       under focus, there is no accessible evar either. EJGA: this
       seems strange, as we have pf *)
    let env = Global.env () in
    Evd.from_env env, env

let get_proof_context p =
  try get_goal_context_gen p 1
  with
  | NoSuchGoal ->
    (* No more focused goals *)
    let { Proof.sigma } = Proof.data p in
    sigma, Global.env ()

let get_current_context pf =
  let p = get_proof pf in
  get_proof_context p
