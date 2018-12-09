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
open Pp
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

let () =
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
  terminator : proof_terminator CEphemeron.key;
  endline_tactic : Genarg.glob_generic_argument option;
  section_vars : Constr.named_context option;
  proof : Proof.t;
  mode : proof_mode CEphemeron.key;
  universe_decl: UState.universe_decl;
  strength : Decl_kinds.goal_kind;
}

type t = pstate list

let make_terminator f = f
let apply_terminator f = f

(* The head of [!pstates] is the actual current proof, the other ones are
   to be resumed when the current proof is closed or aborted. *)
let pstates = ref ([] : pstate list)

(* Current proof_mode, for bookkeeping *)
let current_proof_mode = ref !default_proof_mode

(* combinators for proof modes *)
let update_proof_mode () =
  match !pstates with
  | { mode = m } :: _ ->
      CEphemeron.iter_opt !current_proof_mode (fun x -> x.reset ());
      current_proof_mode := m;
      CEphemeron.iter_opt !current_proof_mode (fun x -> x.set ())
  | _ ->
      CEphemeron.iter_opt !current_proof_mode (fun x -> x.reset ());
      current_proof_mode := find_proof_mode "No"

(* combinators for the current_proof lists *)
let push a l = l := a::!l;
  update_proof_mode ()

exception NoSuchProof
let () = CErrors.register_handler begin function
  | NoSuchProof -> CErrors.user_err Pp.(str "No such proof.")
  | _ -> raise CErrors.Unhandled
end

exception NoCurrentProof
let () = CErrors.register_handler begin function
  | NoCurrentProof -> CErrors.user_err Pp.(str "No focused proof (No proof-editing in progress).")
  | _ -> raise CErrors.Unhandled
end

(*** Proof Global manipulation ***)

let get_all_proof_names () =
  List.map Proof.(function pf -> (data pf.proof).name) !pstates

let cur_pstate () =
  match !pstates with
  | np::_ -> np
  | [] -> raise NoCurrentProof

let give_me_the_proof () = (cur_pstate ()).proof
let give_me_the_proof_opt () = try Some (give_me_the_proof ()) with | NoCurrentProof -> None
let get_current_proof_name () = (Proof.data (cur_pstate ()).proof).Proof.name

let with_current_proof f =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest ->
      let et =
        match p.endline_tactic with
        | None -> Proofview.tclUNIT ()
        | Some tac ->
          let open Geninterp in
          let ist = { lfun = Id.Map.empty; extra = TacStore.empty } in
          let Genarg.GenArg (Genarg.Glbwit tag, tac) = tac in
          let tac = Geninterp.interp tag ist tac in
          Ftactic.run tac (fun _ -> Proofview.tclUNIT ())
      in
      let (newpr,ret) = f et p.proof in
      let p = { p with proof = newpr } in
      pstates := p :: rest;
      ret

let simple_with_current_proof f = with_current_proof (fun t p -> f t p , ())

let compact_the_proof () = simple_with_current_proof (fun _ -> Proof.compact)

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest -> pstates := { p with endline_tactic = Some tac } :: rest

(* spiwack: it might be considered to move error messages away.
    Or else to remove special exceptions from Proof_global.
    Arguments for the former: there is no reason Proof_global is only
    accessed directly through vernacular commands. Error message should be
   pushed to external layers, and so we should be able to have a finer
   control on error message on complex actions. *)
let msg_proofs () =
  match get_all_proof_names () with
    | [] -> (spc () ++ str"(No proof-editing in progress).")
    | l ->  (str"." ++ fnl () ++ str"Proofs currently edited:" ++ spc () ++
               (pr_sequence Id.print l) ++ str".")

let there_is_a_proof () = not (List.is_empty !pstates)
let there_are_pending_proofs () = there_is_a_proof ()
let check_no_pending_proof () =
  if not (there_are_pending_proofs ()) then
    ()
  else begin
    CErrors.user_err
      (str"Proof editing in progress" ++ msg_proofs () ++ fnl() ++
       str"Use \"Abort All\" first or complete proof(s).")
  end

let pf_name_eq id ps =
  let Proof.{ name } = Proof.data ps.proof in
  Id.equal name id

let discard_gen id =
  pstates := List.filter (fun pf -> not (pf_name_eq id pf)) !pstates

let discard {CAst.loc;v=id} =
  let n = List.length !pstates in
  discard_gen id;
  if Int.equal (List.length !pstates) n then
    CErrors.user_err ?loc
      ~hdr:"Pfedit.delete_proof" (str"No such proof" ++ msg_proofs ())

let discard_current () =
  if List.is_empty !pstates then raise NoCurrentProof else pstates := List.tl !pstates

let discard_all () = pstates := []

(* [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
let set_proof_mode m id =
  pstates := List.map
      (fun ps -> if pf_name_eq id ps then { ps with mode = m } else ps)
      !pstates;
  update_proof_mode ()

let set_proof_mode mn =
  set_proof_mode (find_proof_mode mn) (get_current_proof_name ())

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
let start_proof sigma name ?(pl=UState.default_univ_decl) kind goals terminator =
  let initial_state = {
    terminator = CEphemeron.create terminator;
    proof = Proof.start ~name ~poly:(pi2 kind) sigma goals;
    endline_tactic = None;
    section_vars = None;
    mode = find_proof_mode "No";
    universe_decl = pl;
    strength = kind } in
  push initial_state pstates

let start_dependent_proof name ?(pl=UState.default_univ_decl) kind goals terminator =
  let initial_state = {
    terminator = CEphemeron.create terminator;
    proof = Proof.dependent_start ~name ~poly:(pi2 kind) goals;
    endline_tactic = None;
    section_vars = None;
    mode = find_proof_mode "No";
    universe_decl = pl;
    strength = kind } in
  push initial_state pstates

let get_used_variables () = (cur_pstate ()).section_vars
let get_universe_decl () = (cur_pstate ()).universe_decl

let set_used_variables l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  let ctx_set =
    List.fold_right Id.Set.add (List.map NamedDecl.get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe as orig) =
    match entry with
    | LocalAssum (x,_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe)
    | LocalDef (x,bo, ty) as decl ->
       if Id.Set.mem x all_safe then orig else
       let vars = Id.Set.union (vars_of env bo) (vars_of env ty) in
       if Id.Set.subset vars all_safe
       then (decl :: ctx, Id.Set.add x all_safe)
       else (ctx, all_safe) in
  let ctx, _ =
    Environ.fold_named_context aux env ~init:(ctx,ctx_set) in
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest ->
      if not (Option.is_empty p.section_vars) then
        CErrors.user_err Pp.(str "Used section variables can be declared only once");
      pstates := { p with section_vars = Some ctx} :: rest;
      ctx, []

let get_open_goals () =
  let Proof.{ goals; stack; shelf } = Proof.data (cur_pstate ()).proof in
  List.length goals +
    List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) stack) +
    List.length shelf

type closed_proof_output = (Constr.t * Safe_typing.private_constants) list * UState.t

let private_poly_univs =
  let b = ref true in
  let _ = Goptions.(declare_bool_option {
      optdepr = false;
      optname = "use private polymorphic universes for Qed constants";
      optkey = ["Private";"Polymorphic";"Universes"];
      optread = (fun () -> !b);
      optwrite = ((:=) b);
    })
  in
  fun () -> !b

let close_proof ~opaque ~keep_body_ucst_separate ?feedback_id ~now
                (fpl : closed_proof_output Future.computation) =
  let { section_vars; proof; terminator; universe_decl; strength } = cur_pstate () in
  let Proof.{ name; poly; entry; initial_euctx } = Proof.data proof in
  let opaque = match opaque with Opaque -> true | Transparent -> false in
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
        else if poly && opaque && private_poly_univs () then
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let universes = UState.restrict universes used_univs in
          let typus = UState.restrict universes used_univs_typ in
          let udecl = UState.check_univ_decl ~poly typus universe_decl in
          let ubody = Univ.ContextSet.diff
              (UState.context_set universes)
              (UState.context_set typus)
          in
          (udecl, typ), ((body, ubody), eff)
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
      const_entry_opaque = opaque;
      const_entry_universes = univs; }
  in
  let entries = Future.map2 entry_fn fpl Proofview.(initial_goals entry) in
  { id = name; entries = entries; persistence = strength;
    universes },
  fun pr_ending -> CEphemeron.get terminator pr_ending

let return_proof ?(allow_partial=false) () =
 let { proof } = cur_pstate () in
 if allow_partial then begin
  let proofs = Proof.partial_proof proof in
  let Proof.{sigma=evd} = Proof.data proof in
  let eff = Evd.eval_side_effects evd in
  (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
  let proofs = List.map (fun c -> EConstr.Unsafe.to_constr c, eff) proofs in
    proofs, Evd.evar_universe_context evd
 end else
  let Proof.{name=pid;entry} = Proof.data proof in
  let initial_goals = Proofview.initial_goals entry in
  let evd = Proof.return ~pid proof in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
  let proofs =
    List.map (fun (c, _) -> (EConstr.to_constr evd c, eff)) initial_goals in
    proofs, Evd.evar_universe_context evd

let close_future_proof ~opaque ~feedback_id proof =
  close_proof ~opaque ~keep_body_ucst_separate:true ~feedback_id ~now:false proof
let close_proof ~opaque ~keep_body_ucst_separate fix_exn =
  close_proof ~opaque ~keep_body_ucst_separate ~now:true
    (Future.from_val ~fix_exn (return_proof ()))

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
let get_terminator () = CEphemeron.get ( cur_pstate() ).terminator
let set_terminator hook =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: ps -> pstates := { p with terminator = CEphemeron.create hook } :: ps

module V82 = struct
  let get_current_initial_conclusions () =
  let { proof; strength } = cur_pstate () in
  let Proof.{ name; entry } = Proof.data proof in
  let initial = Proofview.initial_goals entry in
  let goals = List.map (fun (o, c) -> c) initial in
  name, (goals, strength)
end

let freeze ~marshallable =
  match marshallable with
  | `Yes ->
      CErrors.anomaly (Pp.str"full marshalling of proof state not supported.")
  | `Shallow -> !pstates
  | `No -> !pstates
let unfreeze s = pstates := s; update_proof_mode ()
let proof_of_state = function { proof }::_ -> proof | _ -> raise NoCurrentProof
let copy_terminators ~src ~tgt =
  assert(List.length src = List.length tgt);
  List.map2 (fun op p -> { p with terminator = op.terminator }) src tgt

let update_global_env pf_info =
  with_current_proof (fun _ p ->
     Proof.in_proof p (fun sigma ->
       let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
       let (p,(status,info)) = Proof.run_tactic (Global.env ()) tac p in
         (p, ())))

(* XXX: Bullet hook, should be really moved elsewhere *)
let () =
  let hook n =
    try
      let prf = give_me_the_proof () in
      (Proof_bullet.suggest prf)
    with NoCurrentProof -> mt ()
  in
  Proofview.set_nosuchgoals_hook hook

