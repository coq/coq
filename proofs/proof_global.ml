(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
    CErrors.error (Format.sprintf "No proof mode named \"%s\"." n)

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
  Goptions.declare_string_option {Goptions.
    optsync = true ;
    optdepr = false;
    optname = "default proof mode" ;
    optkey = ["Default";"Proof";"Mode"] ;
    optread = begin fun () ->
      (CEphemeron.default !default_proof_mode standard).name
    end;
    optwrite = begin fun n ->
      default_proof_mode := find_proof_mode n
    end
  }

(*** Proof Global Environment ***)

(* Extra info on proofs. *)
type lemma_possible_guards = int list list
type proof_universes = Evd.evar_universe_context * Universes.universe_binders option
type universe_binders = Id.t Loc.located list

type proof_object = {
  id : Names.Id.t;
  entries : Safe_typing.private_constants Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
  universes: proof_universes;
}

type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry * proof_universes
  | Proved of Vernacexpr.opacity_flag *
             (Vernacexpr.lident * Decl_kinds.theorem_kind option) option *
              proof_object
type proof_terminator = proof_ending -> unit
type closed_proof = proof_object * proof_terminator

type pstate = {
  pid : Id.t;
  terminator : proof_terminator CEphemeron.key;
  endline_tactic : Tacexpr.raw_tactic_expr option;
  section_vars : Context.section_context option;
  proof : Proof.proof;
  strength : Decl_kinds.goal_kind;
  mode : proof_mode CEphemeron.key;
  universe_binders: universe_binders option;
}

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
let _ = CErrors.register_handler begin function
  | NoSuchProof -> CErrors.error "No such proof."
  | _ -> raise CErrors.Unhandled
end

exception NoCurrentProof
let _ = CErrors.register_handler begin function
  | NoCurrentProof -> CErrors.error "No focused proof (No proof-editing in progress)."
  | _ -> raise CErrors.Unhandled
end

(*** Proof Global manipulation ***)

let get_all_proof_names () =
  List.map (function { pid = id } -> id) !pstates

let cur_pstate () =
  match !pstates with
  | np::_ -> np
  | [] -> raise NoCurrentProof

let give_me_the_proof () = (cur_pstate ()).proof
let get_current_proof_name () = (cur_pstate ()).pid

let interp_tac = ref (fun _ -> assert false)
let set_interp_tac f = interp_tac := f

let with_current_proof f =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest ->
      let et =
        match p.endline_tactic with
        | None -> Proofview.tclUNIT ()
        | Some tac -> !interp_tac tac in
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
               (pr_sequence Nameops.pr_id l) ++ str".")

let there_is_a_proof () = not (List.is_empty !pstates)
let there_are_pending_proofs () = there_is_a_proof ()
let check_no_pending_proof () =
  if not (there_are_pending_proofs ()) then
    ()
  else begin
    CErrors.error (Pp.string_of_ppcmds
      (str"Proof editing in progress" ++ msg_proofs () ++ fnl() ++
       str"Use \"Abort All\" first or complete proof(s)."))
  end

let discard_gen id =
  pstates := List.filter (fun { pid = id' } -> not (Id.equal id id')) !pstates

let discard (loc,id) =
  let n = List.length !pstates in
  discard_gen id;
  if Int.equal (List.length !pstates) n then
    CErrors.user_err_loc
      (loc,"Pfedit.delete_proof",str"No such proof" ++ msg_proofs ())

let discard_current () =
  if List.is_empty !pstates then raise NoCurrentProof else pstates := List.tl !pstates

let discard_all () = pstates := []

(* [set_proof_mode] sets the proof mode to be used after it's called. It is
    typically called by the Proof Mode command. *)
let set_proof_mode m id =
  pstates :=
    List.map (function { pid = id' } as p ->
      if Id.equal id' id then { p with mode = m } else p) !pstates;
  update_proof_mode ()

let set_proof_mode mn =
  set_proof_mode (find_proof_mode mn) (get_current_proof_name ())

let activate_proof_mode mode =
  CEphemeron.iter_opt (find_proof_mode mode) (fun x -> x.set ())
let disactivate_current_proof_mode () =
  CEphemeron.iter_opt !current_proof_mode (fun x -> x.reset ())

(** [start_proof sigma id str goals terminator] starts a proof of name
    [id] with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. The proof is started in the
    evar map [sigma] (which can typically contain universe
    constraints). *)
let start_proof sigma id ?pl str goals terminator =
  let initial_state = {
    pid = id;
    terminator = CEphemeron.create terminator;
    proof = Proof.start sigma goals;
    endline_tactic = None;
    section_vars = None;
    strength = str;
    mode = find_proof_mode "No";
    universe_binders = pl } in
  push initial_state pstates

let start_dependent_proof id ?pl str goals terminator =
  let initial_state = {
    pid = id;
    terminator = CEphemeron.create terminator;
    proof = Proof.dependent_start goals;
    endline_tactic = None;
    section_vars = None;
    strength = str;
    mode = find_proof_mode "No";
    universe_binders = pl } in
  push initial_state pstates

let get_used_variables () = (cur_pstate ()).section_vars
let get_universe_binders () = (cur_pstate ()).universe_binders

let proof_using_auto_clear = ref false
let _ = Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "Proof using Clear Unused";
      Goptions.optkey   = ["Proof";"Using";"Clear";"Unused"];
      Goptions.optread  = (fun () -> !proof_using_auto_clear);
      Goptions.optwrite = (fun b -> proof_using_auto_clear := b) }

let set_used_variables l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  let ctx_set =
    List.fold_right Id.Set.add (List.map get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe, to_clear as orig) =
    match entry with
    | LocalAssum (x,_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe, (Loc.ghost,x)::to_clear) 
    | LocalDef (x,bo, ty) as decl ->
       if Id.Set.mem x all_safe then orig else
       let vars = Id.Set.union (vars_of env bo) (vars_of env ty) in
       if Id.Set.subset vars all_safe
       then (decl :: ctx, Id.Set.add x all_safe, to_clear)
       else (ctx, all_safe, (Loc.ghost,x) :: to_clear) in
  let ctx, _, to_clear =
    Environ.fold_named_context aux env ~init:(ctx,ctx_set,[]) in
  let to_clear = if !proof_using_auto_clear then to_clear else [] in
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: rest ->
      if not (Option.is_empty p.section_vars) then
        CErrors.error "Used section variables can be declared only once";
      pstates := { p with section_vars = Some ctx} :: rest;
      ctx, to_clear

let get_open_goals () =
  let gl, gll, shelf , _ , _ = Proof.proof (cur_pstate ()).proof in
  List.length gl +
    List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) gll) +
    List.length shelf

let constrain_variables init uctx =
  let levels = Univ.Instance.levels (Univ.UContext.instance init) in
  let cstrs = UState.constrain_variables levels uctx in
  Univ.ContextSet.add_constraints cstrs (UState.context_set uctx)

let close_proof ~keep_body_ucst_separate ?feedback_id ~now fpl =
  let { pid; section_vars; strength; proof; terminator; universe_binders } =
    cur_pstate () in
  let poly = pi2 strength (* Polymorphic *) in
  let initial_goals = Proof.initial_goals proof in
  let initial_euctx = Proof.initial_euctx proof in
  let fpl, univs = Future.split2 fpl in
  let universes = if poly || now then Future.force univs else initial_euctx in
  (* Because of dependent subgoals at the beginning of proofs, we could
     have existential variables in the initial types of goals, we need to
     normalise them for the kernel. *)
  let subst_evar k =
    Proof.in_proof proof (fun m -> Evd.existential_opt_value m k) in
  let nf = Universes.nf_evars_and_universes_opt_subst subst_evar
    (Evd.evar_universe_context_subst universes) in
  let make_body =
    if poly || now then
      let make_body t (c, eff) =
        let open Universes in
        let body = c in
	let typ =
	  if not (keep_body_ucst_separate || not (Safe_typing.empty_private_constants = eff)) then
	    nf t
	  else t
	in
        let used_univs_body = Universes.universes_of_constr body in
        let used_univs_typ = Universes.universes_of_constr typ in
        if keep_body_ucst_separate ||
           not (Safe_typing.empty_private_constants = eff) then
          let initunivs = Evd.evar_context_universe_context initial_euctx in
          let ctx = constrain_variables initunivs universes in
          (* For vi2vo compilation proofs are computed now but we need to
           * complement the univ constraints of the typ with the ones of
           * the body.  So we keep the two sets distinct. *)
	  let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let ctx_body = restrict_universe_context ctx used_univs in
          (initunivs, typ), ((body, ctx_body), eff)
        else
          let initunivs = Univ.UContext.empty in
          let ctx = constrain_variables initunivs universes in
          (* Since the proof is computed now, we can simply have 1 set of
           * constraints in which we merge the ones for the body and the ones
           * for the typ *)
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let ctx = restrict_universe_context ctx used_univs in
          let univs = Univ.ContextSet.to_context ctx in
          (univs, typ), ((body, Univ.ContextSet.empty), eff)
      in 
       fun t p -> Future.split2 (Future.chain ~pure:true p (make_body t))
    else
      fun t p ->
        let initunivs = Evd.evar_context_universe_context initial_euctx in
        Future.from_val (initunivs, nf t),
        Future.chain ~pure:true p (fun (pt,eff) ->
          (pt,constrain_variables initunivs (Future.force univs)),eff)
  in
  let entries =
    Future.map2 (fun p (_, t) ->
      let univstyp, body = make_body t p in
      let univs, typ = Future.force univstyp in
	{ Entries.
	  const_entry_body = body;
	  const_entry_secctx = section_vars;
	  const_entry_feedback = feedback_id;
	  const_entry_type  = Some typ;
	  const_entry_inline_code = false;
	  const_entry_opaque = true;
	  const_entry_universes = univs;
	  const_entry_polymorphic = poly})
		fpl initial_goals in
  let binders =
    Option.map (fun names -> fst (Evd.universe_context ~names (Evd.from_ctx universes)))
	       universe_binders
  in
  { id = pid; entries = entries; persistence = strength;
    universes = (universes, binders) },
  fun pr_ending -> CEphemeron.get terminator pr_ending

type closed_proof_output = (Term.constr * Safe_typing.private_constants) list * Evd.evar_universe_context

let return_proof ?(allow_partial=false) () =
 let { pid; proof; strength = (_,poly,_) } = cur_pstate () in
 if allow_partial then begin
  let proofs = Proof.partial_proof proof in
  let _,_,_,_, evd = Proof.proof proof in
  let eff = Evd.eval_side_effects evd in
  (** ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
      side-effects... This may explain why one need to uniquize side-effects
      thereafter... *)
  let proofs = List.map (fun c -> c, eff) proofs in
    proofs, Evd.evar_universe_context evd
 end else
  let initial_goals = Proof.initial_goals proof in
  let evd =
    let error s =
      let prf = str " (in proof " ++ Id.print pid ++ str ")" in
      raise (CErrors.UserError("last tactic before Qed",s ++ prf))
    in
    try Proof.return proof with
    | Proof.UnfinishedProof ->
        error(str"Attempt to save an incomplete proof")
    | Proof.HasShelvedGoals ->
        error(str"Attempt to save a proof with shelved goals")
    | Proof.HasGivenUpGoals ->
        error(strbrk"Attempt to save a proof with given up goals. If this is really what you want to do, use Admitted in place of Qed.")
    | Proof.HasUnresolvedEvar->
        error(strbrk"Attempt to save a proof with existential variables still non-instantiated") in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.nf_constraints evd in
  (** ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
      side-effects... This may explain why one need to uniquize side-effects
      thereafter... *)
  let proofs = 
    List.map (fun (c, _) -> (Evarutil.nf_evars_universes evd c, eff)) initial_goals in
    proofs, Evd.evar_universe_context evd

let close_future_proof ~feedback_id proof =
  close_proof ~keep_body_ucst_separate:true ~feedback_id ~now:false proof
let close_proof ~keep_body_ucst_separate fix_exn =
  close_proof ~keep_body_ucst_separate ~now:true
    (Future.from_val ~fix_exn (return_proof ()))

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
let get_terminator () = CEphemeron.get ( cur_pstate() ).terminator
let set_terminator hook =
  match !pstates with
  | [] -> raise NoCurrentProof
  | p :: ps -> pstates := { p with terminator = CEphemeron.create hook } :: ps




(**********************************************************)
(*                                                        *)
(*                                 Bullets                *)
(*                                                        *)
(**********************************************************)

module Bullet = struct

  type t = Vernacexpr.bullet

  let bullet_eq b1 b2 = match b1, b2 with
  | Vernacexpr.Dash n1, Vernacexpr.Dash n2 -> n1 = n2
  | Vernacexpr.Star n1, Vernacexpr.Star n2 -> n1 = n2
  | Vernacexpr.Plus n1, Vernacexpr.Plus n2 -> n1 = n2
  | _ -> false

  let pr_bullet b =
    match b with
    | Vernacexpr.Dash n -> str (String.make n '-')
    | Vernacexpr.Star n -> str (String.make n '*')
    | Vernacexpr.Plus n -> str (String.make n '+')


  type behavior = {
    name : string;
    put : Proof.proof -> t -> Proof.proof;
    suggest: Proof.proof -> std_ppcmds
  }

  let behaviors = Hashtbl.create 4
  let register_behavior b = Hashtbl.add behaviors b.name b

  (*** initial modes ***)
  let none = {
    name = "None";
    put = (fun x _ -> x);
    suggest = (fun _ -> mt ())
  }
  let _ = register_behavior none

  module Strict = struct
    type suggestion =
    | Suggest of t (* this bullet is mandatory here *)
    | Unfinished of t (* no mandatory bullet here, but this bullet is unfinished *)
    | NoBulletInUse (* No mandatory bullet (or brace) here, no bullet pending,
		       some focused goals exists. *)
    | NeedClosingBrace (* Some unfocussed goal exists "{" needed to focus them *)
    | ProofFinished (* No more goal anywhere *)

    (* give a message only if more informative than the standard coq message *)
    let suggest_on_solved_goal sugg =
      match sugg with
      | NeedClosingBrace -> str"Try unfocusing with \"}\"."
      | NoBulletInUse -> mt ()
      | ProofFinished -> mt ()
      | Suggest b -> str"Focus next goal with bullet " ++ pr_bullet b ++ str"."
      | Unfinished b -> str"The current bullet " ++ pr_bullet b ++ str" is unfinished."

    (* give always a message. *)
    let suggest_on_error sugg =
      match sugg with
      | NeedClosingBrace -> str"Try unfocusing with \"}\"."
      | NoBulletInUse -> assert false (* This should never raise an error. *)
      | ProofFinished -> str"No more subgoals."
      | Suggest b -> str"Bullet " ++ pr_bullet b ++ str" is mandatory here."
      | Unfinished b -> str"Current bullet " ++ pr_bullet b ++ str" is not finished."

    exception FailedBullet of t * suggestion

    let _ =
      CErrors.register_handler
	(function
	| FailedBullet (b,sugg) ->
	  let prefix = str"Wrong bullet " ++ pr_bullet b ++ str" : " in
	  CErrors.errorlabstrm "Focus" (prefix ++ suggest_on_error sugg)
	| _ -> raise CErrors.Unhandled)


    (* spiwack: we need only one focus kind as we keep a stack of (distinct!) bullets *)
    let bullet_kind = (Proof.new_focus_kind () : t list Proof.focus_kind)
    let bullet_cond = Proof.done_cond ~loose_end:true bullet_kind

    (* spiwack: as it is bullets are reset (locally) by *any* non-bullet focusing command
       experience will tell if this is the right discipline of if we want to be finer and
       reset them only for a choice of bullets. *)
    let get_bullets pr =
      if Proof.is_last_focus bullet_kind pr then
	Proof.get_at_focus bullet_kind pr
      else
	[]

    let has_bullet bul pr =
      let rec has_bullet = function
	| b'::_ when bullet_eq bul b' -> true
	| _::l -> has_bullet l
	| [] -> false
      in
      has_bullet (get_bullets pr)

    (* pop a bullet from proof [pr]. There should be at least one
       bullet in use. If pop impossible (pending proofs on this level
       of bullet or higher) then raise [Proof.CannotUnfocusThisWay]. *)
    let pop pr =
      match get_bullets pr with
      | b::_ -> Proof.unfocus bullet_kind pr () , b
      | _ -> assert false

    let push (b:t) pr =
      Proof.focus bullet_cond (b::get_bullets pr) 1 pr

    (* Used only in the next function.
       TODO: use a recursive function instead? *)
    exception SuggestFound of t

    let suggest_bullet (prf:Proof.proof): suggestion =
      if Proof.is_done prf then ProofFinished
      else if not (Proof.no_focused_goal prf)
      then (* No suggestion if a bullet is not mandatory, look for an unfinished bullet *)
	match get_bullets prf with
	| b::_ -> Unfinished b
	| _ -> NoBulletInUse
      else (* There is no goal under focus but some are unfocussed,
	      let us look at the bullet needed. If no  *)
	let pcobaye = ref prf in
	try
	  while true do
	    let pcobaye', b = pop !pcobaye in
	   (* pop went well, this means that there are no more goals
	    *under this* bullet b, see if a new b can be pushed. *)
	    (try let _ = push b pcobaye' in (* push didn't fail so a new b can be pushed. *)
		 raise (SuggestFound b)
	     with SuggestFound _ as e -> raise e
	     | _ -> ()); (* b could not be pushed, so we must look for a outer bullet *)
	    pcobaye := pcobaye'
	  done;
	  assert false
	with SuggestFound b -> Suggest b
	| _ -> NeedClosingBrace (* No push was possible, but there are still
				   subgoals somewhere: there must be a "}" to use. *)


    let rec pop_until (prf:Proof.proof) bul: Proof.proof =
      let prf', b = pop prf in
      if bullet_eq bul b then prf'
      else pop_until prf' bul

    let put p bul =
      try
	if not (has_bullet bul p) then
	  (* bullet is not in use, so pushing it is always ok unless
	     no goal under focus. *)
	  push bul p
	else
	  match suggest_bullet p with
	  | Suggest suggested_bullet when bullet_eq bul suggested_bullet
	      -> (* suggested_bullet is mandatory and you gave the right one *)
	    let p' = pop_until p bul in
	    push bul p'
	(* the bullet you gave is in use but not the right one *)
	  | sugg -> raise (FailedBullet (bul,sugg))
      with Proof.NoSuchGoals _ -> (* push went bad *)
	raise (FailedBullet (bul,suggest_bullet p))

    let strict = {
      name = "Strict Subproofs";
      put = put;
      suggest = (fun prf -> suggest_on_solved_goal (suggest_bullet prf))

    }
    let _ = register_behavior strict
  end

  (* Current bullet behavior, controled by the option *)
  let current_behavior = ref Strict.strict

  let _ =
    Goptions.declare_string_option {Goptions.
      optsync = true;
      optdepr = false;
      optname = "bullet behavior";
      optkey = ["Bullet";"Behavior"];
      optread = begin fun () ->
	(!current_behavior).name
      end;
      optwrite = begin fun n ->
	current_behavior :=
          try Hashtbl.find behaviors n
          with Not_found ->
            CErrors.error ("Unknown bullet behavior: \"" ^ n ^ "\".")
      end
    }

  let put p b =
    (!current_behavior).put p b

  let suggest p =
    (!current_behavior).suggest p
end


let _ =
  let hook n =
    let prf = give_me_the_proof () in
    (Bullet.suggest prf) in
  Proofview.set_nosuchgoals_hook hook


(**********************************************************)
(*                                                        *)
(*                     Default goal selector              *)
(*                                                        *)
(**********************************************************)


(* Default goal selector: selector chosen when a tactic is applied
   without an explicit selector. *)
let default_goal_selector = ref (Vernacexpr.SelectNth 1)
let get_default_goal_selector () = !default_goal_selector

let print_range_selector (i, j) =
  if i = j then string_of_int i
  else string_of_int i ^ "-" ^ string_of_int j

let print_goal_selector = function
  | Vernacexpr.SelectAll -> "all"
  | Vernacexpr.SelectNth i -> string_of_int i
  | Vernacexpr.SelectList l -> "[" ^
      String.concat ", " (List.map print_range_selector l) ^ "]"
  | Vernacexpr.SelectId id -> Id.to_string id

let parse_goal_selector = function
  | "all" -> Vernacexpr.SelectAll
  | i ->
      let err_msg = "The default selector must be \"all\" or a natural number." in
      begin try
              let i = int_of_string i in
              if i < 0 then CErrors.error err_msg;
              Vernacexpr.SelectNth i
        with Failure _ -> CErrors.error err_msg
      end

let _ =
  Goptions.declare_string_option {Goptions.
                                  optsync = true ;
                                  optdepr = false;
                                  optname = "default goal selector" ;
                                  optkey = ["Default";"Goal";"Selector"] ;
                                  optread = begin fun () -> print_goal_selector !default_goal_selector end;
                                  optwrite = begin fun n ->
                                    default_goal_selector := parse_goal_selector n
                                  end
                                 }


module V82 = struct
  let get_current_initial_conclusions () =
  let { pid; strength; proof } = cur_pstate () in
  let initial = Proof.initial_goals proof in
  let goals = List.map (fun (o, c) -> c) initial in
    pid, (goals, strength)
end

type state = pstate list
        
let freeze ~marshallable =
  match marshallable with
  | `Yes ->
      CErrors.anomaly (Pp.str"full marshalling of proof state not supported")
  | `Shallow -> !pstates
  | `No -> !pstates
let unfreeze s = pstates := s; update_proof_mode ()
let proof_of_state = function { proof }::_ -> proof | _ -> raise NoCurrentProof
let copy_terminators ~src ~tgt =
  assert(List.length src = List.length tgt);
  List.map2 (fun op p -> { p with terminator = op.terminator }) src tgt

let update_global_env () =
  with_current_proof (fun _ p ->
     Proof.in_proof p (fun sigma ->
       let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
       let (p,(status,info)) = Proof.run_tactic (Global.env ()) tac p in
         (p, ())))
