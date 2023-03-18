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

let (ltac_trace_info : ltac_stack Exninfo.t) = Exninfo.make ()

let prtac x =
  let env = Global.env () in
  Pptactic.pr_glob_tactic env x

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


type varmap = Geninterp.Val.t Names.Id.Map.t

let fmt_vars1 : varmap list -> int -> DebugHook.Answer.vars = fun varmaps framenum ->
  let varmap = List.nth varmaps framenum in
  let open Names in
  List.map (fun b ->
      let (id, v) = b in
      (Id.to_string id, Pptactic.pr_value Constrexpr.LevelSome v)
    ) (Id.Map.bindings varmap)

(* Communications with the outside world *)
module Comm = struct
  let hook () = Option.get (DebugHook.Intf.get ())
  let wrap = Proofview.NonLogical.make

  (* TODO: ideally we would check that the debugger hooks are
     correctly set, however we don't do this yet as debugger
     initialization is unconditionally done for example in coqc.
     Improving this would require some tweaks in tacinterp which
     are out of scope for the current refactoring. *)
  open DebugHook.Intf
  open DebugHook.Answer

  let prompt g = wrap (fun () -> (hook ()).submit_answer (Prompt g))
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
  let isTerminal = DebugCommon.isTerminal
  let read = wrap DebugCommon.(fun () -> read ())

end

let defer_output = Comm.defer_output

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

let print_loc_tac tac =
  let (desc, loc) = tac_loc tac in
  DebugCommon.print_loc desc loc
[@@@ocaml.warning "+32"]

let cvt_frame f =
    let (loc, k) = f in
    (* todo: compare to explain_ltac_call_trace below *)
    match k with
    | LtacNameCall l -> KerName.to_string l, loc
    | LtacMLCall _ -> "??? LtacMLCall", loc
      (* LtacMLCall should not even show the stack frame, but profiling may need it *)
    | LtacNotationCall l -> "??? LtacNotationCall", loc
      (* LtacNotationCall should not even show the stack frame, but profiling may need it *)
    | LtacAtomCall _ -> "??? LtacAtomCall", loc (* not found in stack *)
    | LtacVarCall (kn, id, e) ->
      let fn_name =
        match kn with
        | Some kn -> KerName.to_string kn
        | None -> "" (* anonymous function *)
      in
      fn_name, loc
    | LtacConstrInterp _ -> "", loc
(*    ) stack *)

let fmt_stack1 : ltac_stack -> unit -> string list = fun frames () ->
  List.map (fun f -> let s, _ = cvt_frame f in s) frames

let save_top_chunk tac varmap trace =
  let {locs; stack; varmaps } =  match trace with
  | Some trace -> trace
  | None -> { locs=[]; stack=[]; varmaps=[]}
  in
  let chunk = (locs, fmt_stack1 stack, fmt_vars1 (varmap :: varmaps)) in  (* todo: tac? *)
  DebugCommon.set_top_chunk chunk CAst.(tac.loc)

(* Prints the goal and the command to be executed *)
let goal_com tac =
  DebugCommon.new_stop_point ();
  Proofview.tclTHEN
    (DebugCommon.db_pr_goals ())
    (if Comm.isTerminal () then
      Proofview.tclLIFT (Comm.output (str "Going to execute:" ++ fnl () ++ prtac tac))
    else
      Proofview.tclLIFT (Proofview.NonLogical.return ()))

(* [run (new_ref _)] gives us a ref shared among [NonLogical.t]
   expressions. It avoids parameterizing everything over a
   reference. *)
let skipped = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let skip = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let idtac_breakpt = Proofview.NonLogical.run (Proofview.NonLogical.ref None)

let batch = ref false

open Goptions

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Ltac";"Batch";"Debug"];
      optread  = (fun () -> !batch);
      optwrite = (fun x -> batch := x) }

(* (Re-)initialize debugger. is_tac controls whether to set the action *)
let db_initialize is_tac =
  let open Proofview.NonLogical in
  let x = (skip:=0) >> (skipped:=0) >> (idtac_breakpt:=None) in
  if is_tac then make DebugCommon.init >> x else x

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
    let nl = if Stdlib.(!batch) then "\n" else "" in
    Comm.print_deferred () >>
    Comm.prompt (tag "message.prompt"
                   @@ fnl () ++ str "TcDebug (" ++ int level ++ str (") > " ^ nl)) >>
    if Stdlib.(!batch) && Comm.isTerminal () then return (DebugOn (level+1)) else
    let exit = (skip:=0) >> (skipped:=0) >> raise (Sys.Break, Exninfo.null) in
    Comm.read >>= fun inst ->  (* read call *)
    let open DebugHook.Action in
    match inst with
    | Continue
    | StepIn
    | StepOver
    | StepOut -> return (DebugOn (level+1))
    | Skip -> return DebugOff
    | Interrupt -> Proofview.NonLogical.print_char '\b' >> exit  (* todo: why the \b? *)
    | Help -> help () >> prompt level
    | UpdBpts updates -> failwith "UpdBpts"  (* handled in init() loop *)
    | Configd -> failwith "Configd" (* handled in init() loop *)
    | GetStack -> failwith "GetStack" (* handled in read() loop *)
    | GetVars _ -> failwith "GetVars" (* handled in read() loop *)
    | RunCnt num -> (skip:=num) >> (skipped:=0) >>
        runnoprint >> return (DebugOn (level+1))
    | RunBreakpoint s -> (idtac_breakpt:=(Some s)) >> (* todo: look in Continue? *)
        runnoprint >> return (DebugOn (level+1))
    | Command _ -> failwith "Command"  (* not possible *)
    | Failed -> prompt level
    | Ignore -> failwith "Ignore" (* not possible *)

[@@@ocaml.warning "-32"]
open Tacexpr

let pr_call_kind n k =
  let (loc, k) = k in
  let kind = (match k with
  | LtacMLCall _ -> "LtacMLCall"
  | LtacNotationCall _ -> "LtacNotationCall"
  | LtacNameCall l ->
    let name = (KerName.to_string l) ^ (DebugCommon.print_loc "" loc) in
    Printf.printf "%s\n%!" name; Feedback.msg_notice (Pp.str name); "LtacNameCall"
  | LtacAtomCall _ -> "LtacAtomCall"
  | LtacVarCall _ -> "LtacVarCall"
  | LtacConstrInterp _ -> "LtacConstrInterp") in
  Printf.printf "stack %d: %s\n%!" n kind

let dump_stack msg stack =
  match stack with
  | Some stack ->
    Printf.printf "%s: stack len = %d\n" msg (StdList.length stack);
    StdList.iteri pr_call_kind stack;
  | None -> ()

let dump_varmaps msg varmaps =
  match varmaps with
  | Some varmaps ->
    List.iter (fun varmap ->
        Printf.printf "%s: varmap len = %d\n" msg (Id.Map.cardinal varmap);
        List.iter (fun b ->
            let (k, b) = b in
            Printf.printf "id = %s\n%!" (Id.to_string k);
            ignore @@ Pptactic.pr_value Constrexpr.LevelSome b (* todo: LevelSome?? *)
            (* b is Geninterp.Val.t Names.Id.Map.t *)
          ) (Id.Map.bindings varmap)
      ) varmaps
  | None -> ()
[@@@ocaml.warning "+32"]

(* Prints the state and waits for an instruction *)
(* spiwack: the only reason why we need to take the continuation [f]
   as an argument rather than returning the new level directly seems to
   be that [f] is wrapped in with "explain_logic_error". I don't think
   it serves any purpose in the current design, so we could just drop
   that. *)
let debug_prompt lev tac f varmap trace =
  (* trace omits the currently-running tactic, so add separately *)
  let runprint = print_run_ctr true in
  let open Proofview.NonLogical in
  let (>=) = Proofview.tclBIND in
  (* What to print and to do next *)
  let newlevel =
    Proofview.tclLIFT !skip >= fun s ->
      save_top_chunk tac varmap trace;
      let stop_here () =
(*
  let locs, stack, varmaps = match trace with
    | Some {locs; stack; varmaps} -> locs, Some stack, Some (varmap :: varmaps)
    | None -> [], None, Some [varmap] in
*)
(*        dump_stack "at debug_prompt" stack;*)
(*        dump_varmaps "at debug_prompt" varmaps;*)
        Proofview.tclTHEN (goal_com tac) (Proofview.tclLIFT (prompt lev))  (* call prompt -> read msg *)
      in
      if DebugCommon.breakpoint_stop CAst.(tac.loc) then (* here *)
        (* todo: skip := 0 *)
        stop_here ()
      else if s > 0 then
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
            if DebugCommon.stepping_stop () then
              stop_here ()
            else
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

(* for ltac1:(tac) *)
let entry_stop_check tac =
  let loc = !DebugCommon.cur_loc in
  let can_stop = match CAst.(tac.v) with (* avoid double stop for ltac1:(xx) *)
  | TacArg _ -> false
  | _ -> true
  in
  if can_stop && (DebugCommon.breakpoint_stop loc || DebugCommon.stepping_stop ()) then begin
    DebugCommon.new_stop_point ();
    let goal_com () =
      Proofview.tclTHEN
        (DebugCommon.db_pr_goals ())
        (Proofview.tclLIFT (Proofview.NonLogical.return ()))
    in
    Proofview.tclTHEN (goal_com ()) (Proofview.tclIGNORE (Proofview.tclLIFT (prompt 0)))
  end else
    Proofview.tclLIFT (Proofview.NonLogical.return ())

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

(** Extracting traces *)

let is_defined_ltac trace =
  let rec aux = function
  | (_, Tacexpr.LtacNameCall f) :: _ -> not (Tacenv.is_ltac_for_ml_tactic f)
  | (_, Tacexpr.LtacNotationCall f) :: _ -> true
  | (_, Tacexpr.LtacAtomCall _) :: _ -> false
  | _ :: tail -> aux tail
  | [] -> false in
  aux (List.rev trace)

let explain_ltac_call_trace last trace =
  let calls = last :: List.rev_map snd trace in
  let pr_call ck = match ck with
    | Tacexpr.LtacNotationCall kn -> quote (Pptactic.pr_alias_key kn)
  | Tacexpr.LtacNameCall cst -> quote (Pptactic.pr_ltac_constant cst)
  | Tacexpr.LtacMLCall t ->
      quote (prtac t)
  | Tacexpr.LtacVarCall (_,id,t) ->
      quote (Id.print id) ++ strbrk " (bound to " ++
        prtac t ++ str ")"
  | Tacexpr.LtacAtomCall te ->
      quote (prtac (CAst.make (Tacexpr.TacAtom te)))
  | Tacexpr.LtacConstrInterp (env, sigma, c, { Ltac_pretype.ltac_constrs = vars }) ->
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

let extract_ltac_trace trace =
  let trace = skip_extensions trace in
  let (_,c),tail = List.sep_last trace in
  if is_defined_ltac trace then
    (* We entered a user-defined tactic,
       we display the trace with location of the call *)
    let msg = hov 0 (explain_ltac_call_trace c tail ++ fnl()) in
    msg
  else
    mt ()

let get_ltac_trace info =
  let ltac_trace = Exninfo.get info ltac_trace_info in
  match ltac_trace with
  | None -> None
  | Some trace -> Some (extract_ltac_trace trace)

let () = CErrors.register_additional_error_info get_ltac_trace
