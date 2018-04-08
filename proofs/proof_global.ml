(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(***********************************************************************)
(*                                                                     *)
(*      This module defines proof facilities relevant to the           *)
(*      toplevel. In particular it defines the global proof            *)
(*      environment.                                                   *)
(*                                                                     *)
(***********************************************************************)

open Util
open Names

module NamedDecl = Context.Named.Declaration

(*** Proof Modes ***)

(* Type of proof modes :
    - A function [set] to set it *from standard mode*
    - A function [reset] to reset the *standard mode* from it *)
type proof_mode_name = string
type proof_mode = {
  name : proof_mode_name ;
  set : unit -> unit ;
  reset : unit -> unit
}

let proof_modes = Hashtbl.create 6
let find_proof_mode n =
  try Hashtbl.find proof_modes n
  with Not_found ->
    CErrors.user_err Pp.(str (Format.sprintf "No proof mode named \"%s\"." n))

let register_proof_mode ({name = n} as m) =
  Hashtbl.add proof_modes n (CEphemeron.create m)

(* initial mode: standard mode *)
let standard = { name = "No" ; set = (fun ()->()) ; reset = (fun () -> ()) }
let _ = register_proof_mode standard

(* Default proof mode, to be set at the beginning of proofs. *)
let default_proof_mode = ref (find_proof_mode "No")

let get_default_proof_mode_name () =
  (CEphemeron.default !default_proof_mode standard).name

let _ =
  Goptions.(declare_string_option {
    optdepr = false;
    optname = "default proof mode" ;
    optkey = ["Default";"Proof";"Mode"] ;
    optread = begin fun () ->
      (CEphemeron.default !default_proof_mode standard).name
    end;
    optwrite = begin fun n ->
      default_proof_mode := find_proof_mode n
    end
  })

(*** Proof Global Environment ***)

(* Extra info on proofs. *)
type lemma_possible_guards = int list list

type proof_object = {
  id : Names.Id.t;
  entries : Safe_typing.private_constants Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
  universes: UState.t;
}

type opacity_flag = Opaque | Transparent

type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry * UState.t
  | Proved of opacity_flag *
              lident option *
              proof_object

type proof_terminator = proof_ending -> unit
type closed_proof = proof_object * proof_terminator

type pstate = {
  pid : Id.t;  (* the name of the theorem whose proof is being constructed *)
  terminator : proof_terminator CEphemeron.key;
  endline_tactic : Genarg.glob_generic_argument option;
  section_vars : Constr.named_context option;
  proof : Proof.t;
  strength : Decl_kinds.goal_kind;
  mode : proof_mode CEphemeron.key;
  universe_decl: UState.universe_decl;
}

(* The head of [t] is the actual current proof, the other ones are
   to be resumed when the current proof is closed or aborted. *)
type t = pstate * pstate list

let pstate_map f (pf, pfl) = (f pf, List.map f pfl)

let make_terminator f = f
let apply_terminator f = f

(* Current proof_mode, for bookkeeping *)
let current_proof_mode = ref !default_proof_mode

(* combinators for proof modes *)
let update_proof_mode ({ mode = m }, _) =
  CEphemeron.iter_opt !current_proof_mode (fun x -> x.reset ());
  current_proof_mode := m;
  CEphemeron.iter_opt !current_proof_mode (fun x -> x.set ())

(* combinators for the current_proof lists *)
let push ?ontop a =
  let res = match ontop with
    | None -> a , []
    | Some (l,ls) -> a, (l :: ls)
  in
  update_proof_mode res;
  res

(*** Proof Global manipulation ***)

let get_all_proof_names pf =
  let (pn, pns) = pstate_map (function { pid = id } -> id) pf in
  pn :: pns

let give_me_the_proof (ps,_) = ps.proof
let get_current_proof_name (ps,_) = ps.pid

let with_current_proof f (ps, psl) =
  let et =
    match ps.endline_tactic with
    | None -> Proofview.tclUNIT ()
    | Some tac ->
      let open Geninterp in
      let ist = { lfun = Id.Map.empty; extra = TacStore.empty } in
      let Genarg.GenArg (Genarg.Glbwit tag, tac) = tac in
      let tac = Geninterp.interp tag ist tac in
      Ftactic.run tac (fun _ -> Proofview.tclUNIT ())
  in
  let (newpr,ret) = f et ps.proof in
  let ps = { ps with proof = newpr } in
  (ps, psl), ret

let simple_with_current_proof f pf =
  let p, () = with_current_proof (fun t p -> f t p , ()) pf in p

let compact_the_proof pf = simple_with_current_proof (fun _ -> Proof.compact) pf

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac (ps, psl) =
  { ps with endline_tactic = Some tac }, psl

let discard {CAst.loc;v=id} (ps, psl) =
  match List.filter (fun { pid = id' } -> not (Id.equal id id')) (ps :: psl) with
  | [] -> None
  | ps :: psl -> Some (ps, psl)

let discard_current (ps, psl) =
  if List.is_empty psl then None else Some List.(hd psl, tl psl)

(* [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
let set_proof_mode m id pf =
  let pf =
    pstate_map (function { pid = id' } as p ->
      if Id.equal id' id then { p with mode = m } else p) pf in
  update_proof_mode pf;
  pf

let set_proof_mode mn pf =
  set_proof_mode (find_proof_mode mn) (get_current_proof_name pf) pf

let activate_proof_mode mode =
  CEphemeron.iter_opt (find_proof_mode mode) (fun x -> x.set ())
let disactivate_current_proof_mode () =
  CEphemeron.iter_opt !current_proof_mode (fun x -> x.reset ())

(** [start_proof sigma id pl str goals terminator] starts a proof of name
    [id] with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. The proof is started in the
    evar map [sigma] (which can typically contain universe
    constraints), and with universe bindings pl. *)
let start_proof ?ontop sigma id ?(pl=UState.default_univ_decl) str goals terminator =
  let initial_state = {
    pid = id;
    terminator = CEphemeron.create terminator;
    proof = Proof.start sigma goals;
    endline_tactic = None;
    section_vars = None;
    strength = str;
    mode = find_proof_mode "No";
    universe_decl = pl } in
  push ?ontop initial_state

let start_dependent_proof ?ontop id ?(pl=UState.default_univ_decl) str goals terminator =
  let initial_state = {
    pid = id;
    terminator = CEphemeron.create terminator;
    proof = Proof.dependent_start goals;
    endline_tactic = None;
    section_vars = None;
    strength = str;
    mode = find_proof_mode "No";
    universe_decl = pl } in
  push ?ontop initial_state

let get_used_variables (pf,_) = pf.section_vars
let get_universe_decl (pf,_) = pf.universe_decl

let proof_using_auto_clear = ref false
let _ = Goptions.declare_bool_option
    { Goptions.optdepr  = false;
      Goptions.optname  = "Proof using Clear Unused";
      Goptions.optkey   = ["Proof";"Using";"Clear";"Unused"];
      Goptions.optread  = (fun () -> !proof_using_auto_clear);
      Goptions.optwrite = (fun b -> proof_using_auto_clear := b) }

let set_used_variables (ps,psl) l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  let ctx_set =
    List.fold_right Id.Set.add (List.map NamedDecl.get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe, to_clear as orig) =
    match entry with
    | LocalAssum (x,_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe, (CAst.make x)::to_clear)
    | LocalDef (x,bo, ty) as decl ->
       if Id.Set.mem x all_safe then orig else
       let vars = Id.Set.union (vars_of env bo) (vars_of env ty) in
       if Id.Set.subset vars all_safe
       then (decl :: ctx, Id.Set.add x all_safe, to_clear)
       else (ctx, all_safe, (CAst.make x) :: to_clear) in
  let ctx, _, to_clear =
    Environ.fold_named_context aux env ~init:(ctx,ctx_set,[]) in
  let to_clear = if !proof_using_auto_clear then to_clear else [] in
  if not (Option.is_empty ps.section_vars) then
    CErrors.user_err Pp.(str "Used section variables can be declared only once");
  ctx, to_clear, ({ ps with section_vars = Some ctx}, psl)

let get_open_goals (ps, _) =
  let gl, gll, shelf , _ , _ = Proof.proof ps.proof in
  List.length gl +
  List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) gll) +
  List.length shelf

type closed_proof_output = (Constr.t * Safe_typing.private_constants) list * UState.t

let close_proof ~keep_body_ucst_separate ?feedback_id ~now ps
                (fpl : closed_proof_output Future.computation) =
  let { pid; section_vars; strength; proof; terminator; universe_decl } = ps in
  let poly = pi2 strength (* Polymorphic *) in
  let initial_goals = Proof.initial_goals proof in
  let initial_euctx = Proof.initial_euctx proof in
  let constrain_variables ctx =
    UState.constrain_variables (fst (UState.context_set initial_euctx)) ctx
  in
  let fpl, univs = Future.split2 fpl in
  let universes = if poly || now then Future.force univs else initial_euctx in
  (* Because of dependent subgoals at the beginning of proofs, we could
     have existential variables in the initial types of goals, we need to
     normalise them for the kernel. *)
  let subst_evar k =
    Proof.in_proof proof (fun m -> Evd.existential_opt_value0 m k) in
  let nf = UnivSubst.nf_evars_and_universes_opt_subst subst_evar
    (UState.subst universes) in
  let make_body =
    if poly || now then
      let make_body t (c, eff) =
        let body = c in
        let allow_deferred =
          not poly && (keep_body_ucst_separate ||
          not (Safe_typing.empty_private_constants = eff))
        in
        let typ = if allow_deferred then t else nf t in
        let used_univs_body = Vars.universes_of_constr body in
        let used_univs_typ = Vars.universes_of_constr typ in
        if allow_deferred then
          let initunivs = UState.const_univ_entry ~poly initial_euctx in
          let ctx = constrain_variables universes in
          (* For vi2vo compilation proofs are computed now but we need to
             complement the univ constraints of the typ with the ones of
             the body.  So we keep the two sets distinct. *)
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let ctx_body = UState.restrict ctx used_univs in
          let univs = UState.check_mono_univ_decl ctx_body universe_decl in
          (initunivs, typ), ((body, univs), eff)
        else
          (* Since the proof is computed now, we can simply have 1 set of
             constraints in which we merge the ones for the body and the ones
             for the typ. We recheck the declaration after restricting with
             the actually used universes.
             TODO: check if restrict is really necessary now. *)
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let ctx = UState.restrict universes used_univs in
          let univs = UState.check_univ_decl ~poly ctx universe_decl in
          (univs, typ), ((body, Univ.ContextSet.empty), eff)
      in 
       fun t p -> Future.split2 (Future.chain p (make_body t))
    else
      fun t p ->
        (* Already checked the univ_decl for the type universes when starting the proof. *)
        let univctx = Entries.Monomorphic_const_entry (UState.context_set universes) in
        Future.from_val (univctx, nf t),
        Future.chain p (fun (pt,eff) ->
          (* Deferred proof, we already checked the universe declaration with
             the initial universes, ensure that the final universes respect
             the declaration as well. If the declaration is non-extensible,
             this will prevent the body from adding universes and constraints. *)
          let bodyunivs = constrain_variables (Future.force univs) in
          let univs = UState.check_mono_univ_decl bodyunivs universe_decl in
          (pt,univs),eff)
  in
  let entry_fn p (_, t) =
    let t = EConstr.Unsafe.to_constr t in
    let univstyp, body = make_body t p in
    let univs, typ = Future.force univstyp in
    {Entries.
      const_entry_body = body;
      const_entry_secctx = section_vars;
      const_entry_feedback = feedback_id;
      const_entry_type  = Some typ;
      const_entry_inline_code = false;
      const_entry_opaque = true;
      const_entry_universes = univs; }
  in
  let entries = Future.map2 entry_fn fpl initial_goals in
  { id = pid; entries = entries; persistence = strength;
    universes },
  fun pr_ending -> CEphemeron.get terminator pr_ending

let return_proof ?(allow_partial=false) (ps,_) =
 let { pid; proof; strength = (_,poly,_) } = ps in
 if allow_partial then begin
  let proofs = Proof.partial_proof proof in
  let _,_,_,_, evd = Proof.proof proof in
  let eff = Evd.eval_side_effects evd in
  (** ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
      side-effects... This may explain why one need to uniquize side-effects
      thereafter... *)
  let proofs = List.map (fun c -> EConstr.Unsafe.to_constr c, eff) proofs in
    proofs, Evd.evar_universe_context evd
 end else
  let initial_goals = Proof.initial_goals proof in
  let evd = Proof.return ~pid proof in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  (** ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
      side-effects... This may explain why one need to uniquize side-effects
      thereafter... *)
  let proofs =
    List.map (fun (c, _) -> (EConstr.to_constr evd c, eff)) initial_goals in
    proofs, Evd.evar_universe_context evd

let close_future_proof ~feedback_id (ps, psl) proof =
  close_proof ~keep_body_ucst_separate:true ~feedback_id ~now:false ps proof

let close_proof ~keep_body_ucst_separate fix_exn (ps, psl) =
  close_proof ~keep_body_ucst_separate ~now:true ps
        (Future.from_val ~fix_exn (return_proof (ps, psl)))

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
let get_terminator (ps, _) = CEphemeron.get ps.terminator
let set_terminator hook (ps, psl) =
  { ps with terminator = CEphemeron.create hook }, psl

module V82 = struct
  let get_current_initial_conclusions (ps,_) =
  let { pid; strength; proof } = ps in
  let initial = Proof.initial_goals proof in
  let goals = List.map (fun (o, c) -> c) initial in
    pid, (goals, strength)
end

let proof_of_state ({proof},_) = proof
let copy_terminators ~src ~tgt =
  let (ps, psl), (ts,tsl) = src, tgt in
  assert(List.length psl = List.length tsl);
  {ts with terminator = ps.terminator}, List.map2 (fun op p -> { p with terminator = op.terminator }) psl tsl

let update_global_env pf =
  let res, () =
  with_current_proof (fun _ p ->
     Proof.in_proof p (fun sigma ->
       let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
       let (p,(status,info)) = Proof.run_tactic (Global.env ()) tac p in
         (p, ()))) pf
  in res

(* XXX: Bullet hook, should be really moved elsewhere *)
(* let _ =
 *   let hook n =
 *     try
 *       let prf = give_me_the_proof pf in
 *       (Proof_bullet.suggest prf)
 *     with NoCurrentProof -> mt ()
 *   in
 *   Proofview.set_nosuchgoals_hook hook *)

