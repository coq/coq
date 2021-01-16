(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StdList = List

open Util
open Names
open Pp
open Tacexpr

let (ltac_trace_info : ltac_trace Exninfo.t) = Exninfo.make ()

let prtac x =
  let env = Global.env () in
  Pptactic.pr_glob_tactic env x
let prmatchpatt env sigma hyp =
  Pptactic.pr_match_pattern (Printer.pr_constr_pattern_env env sigma) hyp
let prmatchrl env sigma rl =
  Pptactic.pr_match_rule false prtac
    (fun (_,p) -> Printer.pr_constr_pattern_env env sigma p) rl

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn of int
  | DebugOff

(* An exception handler *)
let explain_logic_error e = CErrors.print e
let explain_logic_error_no_anomaly e = CErrors.print_no_report e

[@@@ocaml.warning "-32"]
let cmd_to_str cmd =
  let open DebugHook.Action in
  match cmd with
  | Continue -> "Continue"
  | StepIn -> "StepIn"
  | StepOver -> "StepOver"
  | StepOut -> "StepOut"
  | Skip -> "Skip"
  | Interrupt -> "Interrput"
  | Help -> "Help"
  | RunCnt _ -> "RunCnt"
  | RunBreakpoint _ -> "RunBreakpoint"
  | Command _ -> "Command"
  | Failed -> "Failed"
  | Ignore -> "Ignore"
[@@@ocaml.warning "+32"]

let action = ref DebugHook.Action.StepOver

(* Communications with the outside world *)
module Comm = struct

  (* TODO: ideally we would check that the debugger hooks are
     correctly set, however we don't do this yet as debugger
     initialiation is unconditionally done for example in coqc.
     Improving this would require some tweaks in tacinterp which
     are out of scope for the current refactoring. *)
  let init () =
    let open DebugHook in
    match Intf.get () with
    | Some intf ->
      action := if Intf.(intf.isTerminal) then Action.StepIn else Action.Continue;
      Control.break := false;
      ()
    | None -> ()
      (* CErrors.user_err
       *   (Pp.str "Your user interface does not support the Ltac debugger.") *)

  let hook () = Option.get (DebugHook.Intf.get ())
  let wrap = Proofview.NonLogical.make

  open DebugHook.Intf
  open DebugHook.Answer

  let prompt g = wrap (fun () -> (hook ()).submit_answer (Prompt g))
  let goal g = wrap (fun () -> (hook ()).submit_answer (Goal g))
  let output g = wrap (fun () -> (hook ()).submit_answer (Output g))

  (* routines for deferring output; output is sent only if
     the debugger stops at the next step *)
  let out_queue = Queue.create ()
  let defer_output f = wrap (fun () -> Queue.add f out_queue)
  let print_deferred () = wrap (fun () ->
    while not (Queue.is_empty out_queue)
    do
      (hook ()).submit_answer (Output ((Queue.pop out_queue) ()))
    done)
  let clear_queue () = wrap (fun () -> Queue.clear out_queue)

  [@@@ocaml.warning "-32"]
  let print g = (hook ()).submit_answer (Output (str g))
  [@@@ocaml.warning "+32"]
  let isTerminal () = (hook ()).isTerminal
  let read = wrap (fun () ->
    let rec l () =
      let cmd = (hook ()).read_cmd () in
      match cmd with
      | DebugHook.Action.Ignore -> l ()
      | _ -> action := cmd; cmd
    in
    l ())

end

let defer_output = Comm.defer_output

(* Prints the goal *)

let db_pr_goal gl =
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let penv = Termops.Internal.print_named_context env in
  let pc = Printer.pr_econstr_env env (Tacmach.New.project gl) concl in
    str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

let db_pr_goal =
  Proofview.Goal.enter begin fun gl ->
  let pg = db_pr_goal gl in
  Proofview.tclLIFT (Comm.goal pg)
  end

(* Prints the commands *)
let help () =
  Comm.output
    (str "Commands: <Enter> = Step" ++ fnl() ++
     str "          h/? = Help" ++ fnl() ++
     str "          r <num> = Run <num> times" ++ fnl() ++
     str "          r <string> = Run up to next idtac <string>" ++ fnl() ++
     str "          s = Skip" ++ fnl() ++
     str "          x = Exit")

[@@@ocaml.warning "-32"]
let tac_loc tac =
  let open Tacexpr in
  let open CAst in
  let loc, tac = tac.loc, tac.v in
  let rv = match tac with
  | TacAtom _ -> "TacAtom"
  | TacThen _ -> "TacThen"
  | TacDispatch _ -> "TacDispatch"
  | TacExtendTac _ -> "TacExtendTac"
  | TacThens _ -> "TacThens"
  | TacThens3parts _ -> "TacThens3parts"
  | TacFirst _ -> "TacFirst"
  | TacComplete _ -> "TacComplete"
  | TacSolve _ -> "TacSolve"
  | TacTry _ -> "TacTry"
  | TacOr _ -> "TacOr"
  | TacOnce _ -> "TacOnce"
  | TacExactlyOnce _ -> "TacExactlyOnce"
  | TacIfThenCatch _ -> "TacIfThenCatch"
  | TacOrelse _ -> "TacOrelse"
  | TacDo _ -> "TacDo"
  | TacTimeout _ -> "TacTimeout"
  | TacTime _ -> "TacTime"
  | TacRepeat _ -> "TacRepeat"
  | TacProgress _ -> "TacProgress"
  | TacShowHyps _ -> "TacShowHyps"
  | TacAbstract _ -> "TacAbstract"
  | TacId _ -> "TacId"
  | TacFail _ -> "TacFail"
  | TacLetIn _ -> "TacLetIn"
  | TacMatch _ -> "TacMatch"
  | TacMatchGoal _ -> "TacMatchGoal"
  | TacFun _ -> "TacFun"
  | TacArg _ -> "TacArg"
  | TacSelect _ -> "TacSelect"
  | TacML _ -> "TacML"
  | TacAlias _ -> "TacAlias"
  in
(*  Printf.printf "  %s\n%!" (fst rv);*)
  rv, loc

let print_loc tac =
  let open Loc in
  let (desc, loc) = tac_loc tac in
  match loc with
  | Some loc ->
    let src = (match loc.fname with
    | InFile {file} -> file
    | ToplevelInput -> "ToplevelInput")
    in
    Printf.sprintf "%s: %s %d %d:%d\n" desc src loc.line_nb
      (loc.bp - loc.bol_pos_last) (loc.ep - loc.bol_pos_last)
  | None -> Printf.sprintf "%s: loc is None" desc
[@@@ocaml.warning "+32"]

let save_loc tac =
(*  Comm.print (print_loc tac);*)
  DebugHook.(debugger_state.cur_loc <- CAst.(tac.loc))

(* Prints the goal and the command to be executed *)
let goal_com tac =
  save_loc tac;
  Proofview.tclTHEN
    db_pr_goal
    (if Comm.isTerminal () || DebugHook.(debugger_state.cur_loc) = None then
      (Proofview.tclLIFT (Comm.output (str "Going to execute:" ++ fnl () ++ prtac tac)))
    else
      Proofview.tclLIFT (Proofview.NonLogical.return ()))

(* [run (new_ref _)] gives us a ref shared among [NonLogical.t]
   expressions. It avoids parametrizing everything over a
   reference. *)
let skipped = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let skip = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let idtac_breakpt = Proofview.NonLogical.run (Proofview.NonLogical.ref None)

let batch = ref false
let prev_stack = ref (Some [])  (* previous stopping point in debugger *)

open Goptions

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Ltac";"Batch";"Debug"];
      optread  = (fun () -> !batch);
      optwrite = (fun x -> batch := x) }

(* (Re-)initialize debugger. is_tac controls whether to set the action *)
let db_initialize is_tac =
  let open Proofview.NonLogical in
  let x = (skip:=0) >> (skipped:=0) >> (idtac_breakpt:=None) in
  if is_tac then make Comm.init >> x else x

(* Prints the run counter *)
let print_run_ctr print =
  let open Proofview.NonLogical in
  if print then
    begin
      !skipped >>= fun skipped ->
      Comm.output (str "Executed expressions: " ++ int skipped ++ fnl())
    end >>
    !skipped >>= fun x ->
    skipped := x+1
  else
    return ()

(* Prints the prompt *)
let rec prompt level =
  let runnoprint = print_run_ctr false in
    let open Proofview.NonLogical in
    let nl = if Util.(!batch) then "\n" else "" in
    Comm.print_deferred () >>
    Comm.prompt (tag "message.prompt"
                   @@ fnl () ++ str "TcDebug (" ++ int level ++ str (") > " ^ nl)) >>
    if Util.(!batch) && Comm.isTerminal () then return (DebugOn (level+1)) else
    let exit = (skip:=0) >> (skipped:=0) >> raise (Sys.Break, Exninfo.null) in
    Comm.read >>= fun inst ->
    let open DebugHook.Action in
    match inst with
    | Continue
    | StepIn
    | StepOver
    | StepOut -> return (DebugOn (level+1))
    | Skip -> return (DebugOff)
    | Interrupt -> Proofview.NonLogical.print_char '\b' >> exit  (* todo: why the \b? *)
    | Help -> help () >> prompt level
    | RunCnt num -> (skip:=num) >> (skipped:=0) >>
        runnoprint >> return (DebugOn (level+1))
    | RunBreakpoint s -> (idtac_breakpt:=(Some s)) >> (* todo: look in Continue? *)
        runnoprint >> return (DebugOn (level+1))
    | Command _ -> failwith "Command"  (* not possible *)
    | Failed -> prompt level
    | Ignore -> failwith "Ignore" (* not possible *)

let at_breakpoint tac =
  let open DebugHook in
  let open Loc in
  let checkbpt dirpath offset =
(*    Printf.printf "In tactic_debug, dirpath = %s offset = %d\n%!" dirpath bp;*)
    BPSet.mem { dirpath; offset } !breakpoints
  in
  match CAst.(tac.loc) with
  | Some {fname=InFile {dirpath=Some dirpath}; bp} -> checkbpt dirpath bp
  | Some {fname=ToplevelInput;                 bp} -> checkbpt "Top"   bp
  | _ -> false

[@@@ocaml.warning "-32"]
open Tacexpr

let pr_call_kind n k =
  let (loc, k) = k in
  let kind = (match k with
  | LtacMLCall _ -> "LtacMLCall"
  | LtacNotationCall _ -> "LtacNotationCall"
  | LtacNameCall l ->
    let name = KerName.to_string l in
    Printf.printf "%s\n%!" name; Feedback.msg_notice (Pp.str name); "LtacNameCall"
  | LtacAtomCall _ -> "LtacAtomCall"
  | LtacVarCall _ -> "LtacVarCall"
  | LtacConstrInterp _ -> "LtacConstrInterp") in
  Printf.printf "stack %d: %s\n%!" n kind

let dump_stack msg stack =
  match stack with
  | Some stack ->
    let s = Printf.sprintf "%s: stack len = %d" msg (StdList.length stack) in
    Feedback.msg_notice (Pp.str s);
    StdList.iteri pr_call_kind stack;
  | None -> ()
[@@@ocaml.warning "+32"]

(* Prints the state and waits for an instruction *)
(* spiwack: the only reason why we need to take the continuation [f]
   as an argument rather than returning the new level directly seems to
   be that [f] is wrapped in with "explain_logic_error". I don't think
   it serves any purpose in the current design, so we could just drop
   that. *)
let debug_prompt lev tac f stack =
  let runprint = print_run_ctr true in
  let open Proofview.NonLogical in
  let (>=) = Proofview.tclBIND in
  (* What to print and to do next *)
  let newlevel =
    Proofview.tclLIFT !skip >= fun s ->
(*      dump_stack "at debug_prompt" stack;*)
      let stop_here () =
        prev_stack.contents <- stack;
        Proofview.tclTHEN (goal_com tac) (Proofview.tclLIFT (prompt lev))
      in
      let p_stack = prev_stack.contents in
      if action.contents = DebugHook.Action.Continue && at_breakpoint tac then
        (* todo: skip := 0 *)
        stop_here ()
      else if Control.break.contents then begin
        Control.break.contents <- false;
        stop_here ()
      end else if s > 0 then
        Proofview.tclLIFT ((skip := s-1) >>
          runprint >>
          !skip >>= fun new_skip ->
          (if new_skip = 0 then skipped := 0 else return ()) >>
          return (DebugOn (lev+1)))
      else (* todo: move this block before skip logic? *)
        Proofview.tclLIFT !idtac_breakpt >= fun idtac_breakpt ->
          if Option.has_some idtac_breakpt then
            Proofview.tclLIFT(runprint >> return (DebugOn (lev+1)))
          else begin
            let open DebugHook.Action in
            let stop = match action.contents with
              | Continue -> false
              | StepIn   -> true
              | StepOver -> (* todo: cache list lengths for performance? *)
                            let st, st_prev = (Option.default [] stack), (Option.default [] p_stack) in
                            let l_cur, l_prev = StdList.length st, StdList.length st_prev in
                            if l_cur < l_prev || l_cur = 0 || l_prev = 0 then true (* stepped out *)
                            else
                              let peq = StdList.nth st (l_cur - l_prev) == (StdList.hd st_prev) in
                              (l_cur > l_prev && (not peq)) ||  (* stepped out *)
                              (l_cur = l_prev && peq)  (* stepped over *)
              | StepOut  -> let st, st_prev = (Option.default [] stack), (Option.default [] p_stack) in
                              let l_cur, l_prev = StdList.length st, StdList.length st_prev in
                              if l_cur < l_prev then true
                              else
                                StdList.nth st (l_cur - l_prev) != (StdList.hd st_prev)
              | _ -> failwith "action op"
            in
            if stop then begin
              stop_here ()
            end else
              Proofview.tclLIFT (Comm.clear_queue () >>
              return (DebugOn (lev+1)))
          end
    in
  newlevel >= fun newlevel ->
  (* What to execute *)
  Proofview.tclOR
    (f newlevel)
    begin fun (reraise, info) ->
      Proofview.tclTHEN
        (Proofview.tclLIFT begin
          (skip:=0) >> (skipped:=0) >>
          Comm.defer_output (fun () -> str "Level " ++ int lev ++ str ": " ++ explain_logic_error reraise)
        end)
        (Proofview.tclZERO ~info reraise)
    end

let is_debug db =
  let open Proofview.NonLogical in
  !idtac_breakpt >>= fun idtac_breakpt ->
  match db, idtac_breakpt with
  | DebugOff, _ -> return false
  | _, Some _ -> return false
  | _ ->
      !skip >>= fun skip ->
      return (skip = 0)

(* Prints a constr *)
let db_constr debug env sigma c =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    Comm.defer_output (fun () -> str "Evaluated term: " ++ Printer.pr_econstr_env env sigma c)
  else return ()

(* Prints the pattern rule *)
let db_pattern_rule debug env sigma num r =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
  begin
    Comm.defer_output (fun () ->
        str "Pattern rule " ++ int num ++ str ":" ++ fnl () ++
        str "|" ++ spc () ++ prmatchrl env sigma r)
  end
  else return ()

(* Prints the hypothesis pattern identifier if it exists *)
let hyp_bound = function
  | Anonymous -> str " (unbound)"
  | Name id -> str " (bound to " ++ Id.print id ++ str ")"

(* Prints a matched hypothesis *)
let db_matched_hyp debug env sigma (id,_,c) ido =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    Comm.defer_output (fun () ->
      str "Hypothesis " ++ Id.print id ++ hyp_bound ido ++
      str " has been matched: " ++ Printer.pr_econstr_env env sigma c)
  else return ()

(* Prints the matched conclusion *)
let db_matched_concl debug env sigma c =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    Comm.defer_output (fun () ->
      str "Conclusion has been matched: " ++ Printer.pr_econstr_env env sigma c)
  else return ()

(* Prints a success message when the goal has been matched *)
let db_mc_pattern_success debug =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    Comm.defer_output (fun () ->
      str "The goal has been successfully matched!" ++ fnl() ++
      str "Let us execute the right-hand side part..." ++ fnl())
  else return ()

(* Prints a failure message for a hypothesis pattern *)
let db_hyp_pattern_failure debug env sigma (na,hyp) =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    Comm.defer_output (fun () ->
      str "The pattern hypothesis" ++ hyp_bound na ++
      str " cannot match: " ++
      prmatchpatt env sigma hyp)
  else return ()

(* Prints a matching failure message for a rule *)
let db_matching_failure debug =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    Comm.defer_output (fun () ->
      str "This rule has failed due to matching errors!" ++ fnl() ++
      str "Let us try the next one...")
  else return ()

(* Prints an evaluation failure message for a rule *)
let db_eval_failure debug s =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    let s = str "message \"" ++ s ++ str "\"" in
    Comm.defer_output (fun () ->
      str "This rule has failed due to \"Fail\" tactic (" ++
      s ++ str ", level 0)!" ++ fnl() ++ str "Let us try the next one...")
  else return ()

(* Prints a logic failure message for a rule *)
let db_logic_failure debug err =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
  begin
    Comm.defer_output (fun () -> explain_logic_error err) >>
    Comm.defer_output (fun () ->
      str "This rule has failed due to a logic error!" ++ fnl() ++
      str "Let us try the next one...")
  end
  else return ()

let is_breakpoint brkname s = match brkname, s with
  | Some s, MsgString s'::_ -> String.equal s s'
  | _ -> false

let db_breakpoint debug s =
  let open Proofview.NonLogical in
  !idtac_breakpt >>= fun opt_breakpoint ->
  match debug with
  | DebugOn lev when not (CList.is_empty s) && is_breakpoint opt_breakpoint s ->
      idtac_breakpt:=None
  | _ ->
      return ()

(** Extrating traces *)

let is_defined_ltac trace =
  let rec aux = function
  | (_, Tacexpr.LtacNameCall f) :: _ -> not (Tacenv.is_ltac_for_ml_tactic f)
  | (_, Tacexpr.LtacNotationCall f) :: _ -> true
  | (_, Tacexpr.LtacAtomCall _) :: _ -> false
  | _ :: tail -> aux tail
  | [] -> false in
  aux (List.rev trace)

let explain_ltac_call_trace last trace loc =
  let calls = last :: List.rev_map snd trace in
  let pr_call ck = match ck with
    | Tacexpr.LtacNotationCall kn -> quote (Pptactic.pr_alias_key kn)
  | Tacexpr.LtacNameCall cst -> quote (Pptactic.pr_ltac_constant cst)
  | Tacexpr.LtacMLCall t ->
      quote (prtac t)
  | Tacexpr.LtacVarCall (id,t) ->
      quote (Id.print id) ++ strbrk " (bound to " ++
        prtac t ++ str ")"
  | Tacexpr.LtacAtomCall te ->
      quote (prtac (CAst.make (Tacexpr.TacAtom te)))
  | Tacexpr.LtacConstrInterp (c, { Ltac_pretype.ltac_constrs = vars }) ->
    (* XXX: This hooks into the CErrors's additional error info API so
       it is tricky to provide the right env for now. *)
      let env = Global.env() in
      let sigma = Evd.from_env env in
      quote (Printer.pr_glob_constr_env env sigma c) ++
        (if not (Id.Map.is_empty vars) then
          strbrk " (with " ++
            prlist_with_sep pr_comma
            (fun (id,c) ->
              Id.print id ++ str ":=" ++ Printer.pr_lconstr_under_binders_env env sigma c)
            (List.rev (Id.Map.bindings vars)) ++ str ")"
        else mt())
  in
  match calls with
  | [] -> mt ()
  | [a] -> hov 0 (str "Ltac call to " ++ pr_call a ++ str " failed.")
  | _ ->
    let kind_of_last_call = match List.last calls with
    | Tacexpr.LtacConstrInterp _ -> ", last term evaluation failed."
    | _ -> ", last call failed."
    in
    hov 0 (str "In nested Ltac calls to " ++
           pr_enum pr_call calls ++ strbrk kind_of_last_call)

let skip_extensions trace =
  let rec aux = function
  | (_,Tacexpr.LtacNotationCall _ as tac) :: (_,Tacexpr.LtacMLCall _) :: tail ->
     (* Case of an ML defined tactic with entry of the form <<"foo" args>> *)
     (* see tacextend.mlp *)
     tac :: aux tail
  | t :: tail -> t :: aux tail
  | [] -> [] in
  List.rev (aux (List.rev trace))

let extract_ltac_trace ?loc trace =
  let trace = skip_extensions trace in
  let (tloc,c),tail = List.sep_last trace in
  if is_defined_ltac trace then
    (* We entered a user-defined tactic,
       we display the trace with location of the call *)
    let msg = hov 0 (explain_ltac_call_trace c tail loc ++ fnl()) in
    (if Loc.finer loc tloc then loc else tloc), msg
  else
    (* We entered a primitive tactic, we don't display trace but
       report on the finest location *)
    let best_loc =
      (* trace is with innermost call coming first *)
      let rec aux best_loc = function
        | (loc,_)::tail ->
           if Option.is_empty best_loc ||
              not (Option.is_empty loc) && Loc.finer loc best_loc
           then
             aux loc tail
           else
             aux best_loc tail
        | [] -> best_loc in
        aux loc trace in
    best_loc, mt ()

let get_ltac_trace info =
  let ltac_trace = Exninfo.get info ltac_trace_info in
  let loc = Loc.get_loc info in
  match ltac_trace with
  | None -> None
  | Some trace -> Some (extract_ltac_trace ?loc trace)

let () = CErrors.register_additional_error_info get_ltac_trace
