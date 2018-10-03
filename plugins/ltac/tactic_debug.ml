(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Pp
open Tacexpr

let (ltac_trace_info : ltac_trace Exninfo.t) = Exninfo.make ()

let prtac x =
  Pptactic.pr_glob_tactic (Global.env()) x
let prmatchpatt env sigma hyp =
  Pptactic.pr_match_pattern (Printer.pr_constr_pattern_env env sigma) hyp
let prmatchrl rl =
  Pptactic.pr_match_rule false (Pptactic.pr_glob_tactic (Global.env()))
    (fun (_,p) ->
       let sigma, env = Pfedit.get_current_context () in
       Printer.pr_constr_pattern_env env sigma p) rl

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn of int
  | DebugOff

(* An exception handler *)
let explain_logic_error e =
  CErrors.print (fst (ExplainErr.process_vernac_interp_error (e, Exninfo.null)))

let explain_logic_error_no_anomaly e =
  CErrors.print_no_report
    (fst (ExplainErr.process_vernac_interp_error (e, Exninfo.null)))

let msg_tac_debug s = Proofview.NonLogical.print_debug (s++fnl())
let msg_tac_notice s = Proofview.NonLogical.print_notice (s++fnl())

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
  Proofview.Goal.nf_enter begin fun gl ->
  let pg = db_pr_goal gl in
  Proofview.tclLIFT (msg_tac_notice (str "Goal:" ++ fnl () ++ pg))
  end


(* Prints the commands *)
let help () =
  msg_tac_debug (str "Commands: <Enter> = Continue" ++ fnl() ++
         str "          h/? = Help" ++ fnl() ++
         str "          r <num> = Run <num> times" ++ fnl() ++
         str "          r <string> = Run up to next idtac <string>" ++ fnl() ++
         str "          s = Skip" ++ fnl() ++
         str "          x = Exit")

(* Prints the goal and the command to be executed *)
let goal_com tac =
  Proofview.tclTHEN
    db_pr_goal
    (Proofview.tclLIFT (msg_tac_debug (str "Going to execute:" ++ fnl () ++ prtac tac)))

(* [run (new_ref _)] gives us a ref shared among [NonLogical.t]
   expressions. It avoids parametrizing everything over a
   reference. *)
let skipped = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let skip = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let breakpoint = Proofview.NonLogical.run (Proofview.NonLogical.ref None)

let batch = ref false

open Goptions

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "Ltac batch debug";
      optkey   = ["Ltac";"Batch";"Debug"];
      optread  = (fun () -> !batch);
      optwrite = (fun x -> batch := x) }

let rec drop_spaces inst i =
  if String.length inst > i && inst.[i] == ' ' then drop_spaces inst (i+1)
  else i

let possibly_unquote s =
  if String.length s >= 2 && s.[0] == '"' && s.[String.length s - 1] == '"' then
    String.sub s 1 (String.length s - 2)
  else
    s

(* (Re-)initialize debugger *)
let db_initialize =
  let open Proofview.NonLogical in
  (skip:=0) >> (skipped:=0) >> (breakpoint:=None)

let int_of_string s =
  try Proofview.NonLogical.return (int_of_string s)
  with e -> Proofview.NonLogical.raise e

let string_get s i =
  try Proofview.NonLogical.return (String.get s i)
  with e -> Proofview.NonLogical.raise e

let run_invalid_arg () = Proofview.NonLogical.raise (Invalid_argument "run_com")

(* Gives the number of steps or next breakpoint of a run command *)
let run_com inst =
  let open Proofview.NonLogical in
  string_get inst 0 >>= fun first_char ->
  if first_char ='r' then
    let i = drop_spaces inst 1 in
    if String.length inst > i then
      let s = String.sub inst i (String.length inst - i) in
      if inst.[0] >= '0' && inst.[0] <= '9' then
        int_of_string s >>= fun num ->
        (if num<0 then run_invalid_arg () else return ()) >>
        (skip:=num) >> (skipped:=0)
      else
        breakpoint:=Some (possibly_unquote s)
    else
      run_invalid_arg ()
  else
    run_invalid_arg ()

(* Prints the run counter *)
let run ini =
  let open Proofview.NonLogical in
  if not ini then
    begin
      Proofview.NonLogical.print_notice (str"\b\r\b\r") >>
      !skipped >>= fun skipped ->
      msg_tac_debug (str "Executed expressions: " ++ int skipped ++ fnl())
    end >>
    !skipped >>= fun x ->
    skipped := x+1
  else
    return ()

(* Prints the prompt *)
let rec prompt level =
  (* spiwack: avoid overriding by the open below *)
  let runtrue = run true in
  begin
    let open Proofview.NonLogical in
    Proofview.NonLogical.print_notice (fnl () ++ str "TcDebug (" ++ int level ++ str ") > ") >>
    if Pervasives.(!batch) then return (DebugOn (level+1)) else
    let exit = (skip:=0) >> (skipped:=0) >> raise Sys.Break in
    Proofview.NonLogical.catch Proofview.NonLogical.read_line
      begin function (e, info) -> match e with
        | End_of_file -> exit
        | e -> raise ~info e
      end
    >>= fun inst ->
    match inst with
    | ""  -> return (DebugOn (level+1))
    | "s" -> return (DebugOff)
    | "x" -> Proofview.NonLogical.print_char '\b' >> exit
    | "h"| "?" ->
      begin
        help () >>
        prompt level
      end
    | _ ->
        Proofview.NonLogical.catch (run_com inst >> runtrue >> return (DebugOn (level+1)))
          begin function (e, info) -> match e with
            | Failure _ | Invalid_argument _ -> prompt level
            | e -> raise ~info e
          end
  end

(* Prints the state and waits for an instruction *)
(* spiwack: the only reason why we need to take the continuation [f]
   as an argument rather than returning the new level directly seems to
   be that [f] is wrapped in with "explain_logic_error". I don't think
   it serves any purpose in the current design, so we could just drop
   that. *)
let debug_prompt lev tac f =
  (* spiwack: avoid overriding by the open below *)
  let runfalse = run false in
  let open Proofview.NonLogical in
  let (>=) = Proofview.tclBIND in
  (* What to print and to do next *)
  let newlevel =
    Proofview.tclLIFT !skip >= fun initial_skip ->
    if Int.equal initial_skip 0 then
      Proofview.tclLIFT !breakpoint >= fun breakpoint ->
      if Option.is_empty breakpoint then Proofview.tclTHEN (goal_com tac) (Proofview.tclLIFT (prompt lev))
      else Proofview.tclLIFT(runfalse >> return (DebugOn (lev+1)))
    else Proofview.tclLIFT begin
      (!skip >>= fun s -> skip:=s-1) >>
      runfalse >>
      !skip >>= fun new_skip ->
      (if Int.equal new_skip 0 then skipped:=0 else return ()) >>
      return (DebugOn (lev+1))
    end in
  newlevel >= fun newlevel ->
  (* What to execute *)
  Proofview.tclOR
    (f newlevel)
    begin fun (reraise, info) ->
      Proofview.tclTHEN
        (Proofview.tclLIFT begin
          (skip:=0) >> (skipped:=0) >>
            if Logic.catchable_exception reraise then
              msg_tac_debug (str "Level " ++ int lev ++ str ": " ++ explain_logic_error reraise)
            else return ()
        end)
        (Proofview.tclZERO ~info reraise)
    end

let is_debug db =
  let open Proofview.NonLogical in
  !breakpoint >>= fun breakpoint ->
  match db, breakpoint with
  | DebugOff, _ -> return false
  | _, Some _ -> return false
  | _ ->
      !skip >>= fun skip ->
      return (Int.equal skip 0)

(* Prints a constr *)
let db_constr debug env sigma c =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "Evaluated term: " ++ Printer.pr_econstr_env env sigma c)
  else return ()

(* Prints the pattern rule *)
let db_pattern_rule debug num r =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
  begin
    msg_tac_debug (str "Pattern rule " ++ int num ++ str ":" ++ fnl () ++
      str "|" ++ spc () ++ prmatchrl r)
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
    msg_tac_debug (str "Hypothesis " ++ Id.print id ++ hyp_bound ido ++
                str " has been matched: " ++ Printer.pr_econstr_env env sigma c)
  else return ()

(* Prints the matched conclusion *)
let db_matched_concl debug env sigma c =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "Conclusion has been matched: " ++ Printer.pr_econstr_env env sigma c)
  else return ()

(* Prints a success message when the goal has been matched *)
let db_mc_pattern_success debug =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "The goal has been successfully matched!" ++ fnl() ++
           str "Let us execute the right-hand side part..." ++ fnl())
  else return ()

(* Prints a failure message for an hypothesis pattern *)
let db_hyp_pattern_failure debug env sigma (na,hyp) =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "The pattern hypothesis" ++ hyp_bound na ++
                str " cannot match: " ++
           prmatchpatt env sigma hyp)
  else return ()

(* Prints a matching failure message for a rule *)
let db_matching_failure debug =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    msg_tac_debug (str "This rule has failed due to matching errors!" ++ fnl() ++
           str "Let us try the next one...")
  else return ()

(* Prints an evaluation failure message for a rule *)
let db_eval_failure debug s =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
    let s = str "message \"" ++ s ++ str "\"" in
    msg_tac_debug
      (str "This rule has failed due to \"Fail\" tactic (" ++
       s ++ str ", level 0)!" ++ fnl() ++ str "Let us try the next one...")
  else return ()

(* Prints a logic failure message for a rule *)
let db_logic_failure debug err =
  let open Proofview.NonLogical in
  is_debug debug >>= fun db ->
  if db then
  begin
    msg_tac_debug (explain_logic_error err) >>
    msg_tac_debug (str "This rule has failed due to a logic error!" ++ fnl() ++
           str "Let us try the next one...")
  end
  else return ()

let is_breakpoint brkname s = match brkname, s with
  | Some s, MsgString s'::_ -> String.equal s s'
  | _ -> false

let db_breakpoint debug s =
  let open Proofview.NonLogical in
  !breakpoint >>= fun opt_breakpoint ->
  match debug with
  | DebugOn lev when not (CList.is_empty s) && is_breakpoint opt_breakpoint s ->
      breakpoint:=None
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
      quote (Pptactic.pr_glob_tactic (Global.env()) t)
  | Tacexpr.LtacVarCall (id,t) ->
      quote (Id.print id) ++ strbrk " (bound to " ++
        Pptactic.pr_glob_tactic (Global.env()) t ++ str ")"
  | Tacexpr.LtacAtomCall te ->
      quote (Pptactic.pr_glob_tactic (Global.env())
              (Tacexpr.TacAtom (Loc.tag te)))
  | Tacexpr.LtacConstrInterp (c, { Ltac_pretype.ltac_constrs = vars }) ->
      quote (Printer.pr_glob_constr_env (Global.env()) c) ++
        (if not (Id.Map.is_empty vars) then
          strbrk " (with " ++
            prlist_with_sep pr_comma
            (fun (id,c) ->
              let sigma, env = Pfedit.get_current_context () in
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
    (if Loc.finer loc tloc then loc else tloc), Some msg
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
    best_loc, None

let get_ltac_trace (_, info) =
  let ltac_trace = Exninfo.get info ltac_trace_info in
  let loc = Loc.get_loc info in
  match ltac_trace with
  | None -> None
  | Some trace -> Some (extract_ltac_trace ?loc trace)

let () = ExplainErr.register_additional_error_info get_ltac_trace
