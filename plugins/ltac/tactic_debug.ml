(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

let (ltac_trace_info : ltac_stack Exninfo.t) = Exninfo.make "ltac_trace"

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


type breakpoint = {
  dirpath : string;  (* module dirpath *)
  offset : int;
}

module BPSet = CSet.Make(struct
  type t = breakpoint
  let compare b1 b2 =
    let c1 = Int.compare b1.offset b2.offset in
    if c1 <> 0 then c1 else String.compare b1.dirpath b2.dirpath
  end)

let breakpoints = ref BPSet.empty


(** add or remove a single breakpoint.  Maps the breakpoint from
  IDE format (absolute path name, offset) to (module dirpath, offset)
  opt - true to add, false to remove
  ide_bpt - the breakpoint (absolute path name, offset)
  *)
let update_bpt fname offset opt =
  let open Names in
  let dp =
    if fname = "ToplevelInput" then  (* todo: or None? *)
      DirPath.make [Id.of_string "Top"]
    else begin (* find the DirPath matching the absolute pathname of the file *)
      (* ? check for .v extension? *)
      let dirname = Filename.dirname fname in
      let basename = Filename.basename fname in
      let base_id = Id.of_string (Filename.remove_extension basename) in
      DirPath.make (base_id ::
          (try
            let p = Loadpath.find_load_path (CUnix.physical_path_of_string dirname) in
            DirPath.repr (Loadpath.logical p)
          with exn when CErrors.noncritical exn -> []))
    end
  in
  let dirpath = DirPath.to_string dp in
  let bp = { dirpath; offset } in
(*  Printf.printf "update_bpt: %s -> %s  %d\n%!" fname dirpath ide_bpt.offset;*)
  match opt with
  | true  -> breakpoints := BPSet.add bp !breakpoints
  | false -> breakpoints := BPSet.remove bp !breakpoints

let upd_bpts updates =
  List.iter (fun op ->
    let ((file, offset), opt) = op in
    update_bpt file offset opt;
  ) updates

type debugger_state = {
  (* location of next code to execute, is not in stack *)
  mutable cur_loc : Loc.t option;
  (* yields the call stack *)
  mutable stack : (string * Loc.t option) list;
  (* variable value maps for each stack frame *)
  mutable varmaps : Geninterp.Val.t Names.Id.Map.t list;
}

let debugger_state = { cur_loc=None; stack=[]; varmaps=[] }

let get_stack () =
(*  Printf.printf "server: db_stack call\n%!";*)
  let rec shift s prev_loc res =
    match s with
    | (tacn, loc) :: tl ->
      shift tl loc (((Some tacn), prev_loc) :: res)
    | [] -> (None, prev_loc) :: res
  in
  List.rev (shift debugger_state.stack debugger_state.cur_loc [])

module CSet = CSet.Make (Names.DirPath)
let bad_dirpaths = ref CSet.empty

(* cvt_loc, format_frame and format_stack belong elsewhere *)
let cvt_loc loc =
  let open Loc in
  match loc with
  | Some {fname=ToplevelInput; bp; ep} ->
    Some ("ToplevelInput", [bp; ep])
  | Some {fname=InFile {dirpath=None; file}; bp; ep} ->
    Some (file, [bp; ep])  (* for Load command *)
  | Some {fname=InFile {dirpath=(Some dirpath)}; bp; ep} ->
    let open Names in
    let dirpath = DirPath.make (List.rev_map (fun i -> Id.of_string i)
      (String.split_on_char '.' dirpath)) in
    let pfx = DirPath.make (List.tl (DirPath.repr dirpath)) in
    let paths = Loadpath.find_with_logical_path pfx in
    let basename = match DirPath.repr dirpath with
    | hd :: tl -> (Id.to_string hd) ^ ".v"
    | [] -> ""
    in
    let vs_files = List.map (fun p -> (Filename.concat (Loadpath.physical p) basename)) paths in
    let filtered = List.filter (fun p -> Sys.file_exists p) vs_files in
    begin match filtered with
    | [] -> (* todo: maybe tweak this later to allow showing a popup dialog in the GUI *)
      if not (CSet.mem dirpath !bad_dirpaths) then begin
        bad_dirpaths := CSet.add dirpath !bad_dirpaths;
        let msg = Pp.(fnl () ++ str "Unable to locate source code for module " ++
                        str (Names.DirPath.to_string dirpath)) in
        let msg = if vs_files = [] then msg else
          (List.fold_left (fun msg f -> msg ++ fnl() ++ str f) (msg ++ str " in:") vs_files) in
        Feedback.msg_warning msg
      end;
      None
    | [f] -> Some (f, [bp; ep])
    | f :: tl ->
      if not (CSet.mem dirpath !bad_dirpaths) then begin
        bad_dirpaths := CSet.add dirpath !bad_dirpaths;
        let msg = Pp.(fnl () ++ str "Multiple files found matching module " ++
            str (Names.DirPath.to_string dirpath) ++ str ":") in
        let msg = List.fold_left (fun msg f -> msg ++ fnl() ++ str f) msg vs_files in
        Feedback.msg_warning msg
      end;
      Some (f, [bp; ep]) (* be arbitrary unless we can tell which file was loaded *)
    end
  | None -> None (* nothing to highlight, e.g. not in a .v file *)

 let format_frame text loc =
   try
     let open Loc in
       match loc with
       | Some { fname=InFile {dirpath=(Some dp)}; line_nb } ->
         let dplen = String.length dp in
         let lastdot = String.rindex dp '.' in
         let file = String.sub dp (lastdot+1) (dplen - (lastdot + 1)) in
         let module_name = String.sub dp 0 lastdot in
         let routine =
           (* try text as a kername *)
           if not (CString.is_prefix dp text) then text else
             try
               let knlen = String.length text in
               let lastdot = String.rindex text '.' in
               String.sub text (lastdot+1) (knlen - (lastdot + 1))
             with Not_found -> text
         in
         Printf.sprintf "%s:%d, %s  (%s)" routine line_nb file module_name;
       | Some { fname=ToplevelInput; line_nb } ->
         let items = String.split_on_char '.' text in
         Printf.sprintf "%s:%d, %s" (List.nth items 1) line_nb (List.hd items);
       | _ -> text
   with Not_found -> text

let format_stack s =
  List.map (fun (tac, loc) ->
      let floc = cvt_loc loc in
      match tac with
      | Some tacn ->
        let tacn = if loc = None then
          tacn ^ " (no location)"
        else
          format_frame tacn loc in
        (tacn, floc)
      | None ->
        match loc with
        | Some { Loc.line_nb } ->
          (":" ^ (string_of_int line_nb), floc)
        | None -> (": (no location)", floc)
    ) s


let get_vars framenum =
  let open Names in
(*  Printf.printf "server: db_vars call\n%!";*)
  let vars = List.nth debugger_state.varmaps framenum in
  List.map (fun b ->
      let (id, v) = b in
      (Id.to_string id, Pptactic.pr_value Constrexpr.LevelSome v)
    ) (Id.Map.bindings vars)

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
  | UpdBpts _ -> "UpdBpts"
  | Configd -> "Configd"
  | GetStack -> "GetStack"
  | GetVars _ -> "GetVars"
  | RunCnt _ -> "RunCnt"
  | RunBreakpoint _ -> "RunBreakpoint"
  | Command _ -> "Command"
  | Failed -> "Failed"
  | Ignore -> "Ignore"
[@@@ocaml.warning "+32"]

let action = ref DebugHook.Action.StepOver

let break = ref false
(* causes the debugger to stop at the next step *)

let get_break () = !break
let set_break b = break := b

(* Communications with the outside world *)
module Comm = struct
  let hook () = Option.get (DebugHook.Intf.get ())
  let wrap = Proofview.NonLogical.make

  (* TODO: ideally we would check that the debugger hooks are
     correctly set, however we don't do this yet as debugger
     initialization is unconditionally done for example in coqc.
     Improving this would require some tweaks in tacinterp which
     are out of scope for the current refactoring. *)
  let init () =
    let open DebugHook in
    match Intf.get () with
    | Some intf ->
      if Intf.(intf.isTerminal) then
        action := Action.StepIn
      else begin
        set_break false;
        breakpoints := BPSet.empty;
        (hook ()).Intf.submit_answer (Answer.Init);
        while
          let cmd = (hook ()).Intf.read_cmd () in
          let open DebugHook.Action in
          match cmd with
          | UpdBpts updates -> upd_bpts updates; true
          | Configd -> action := Action.Continue; false
          | _ -> failwith "Action type not allowed"
        do () done
      end
    | None -> ()
      (* CErrors.user_err
       *   (Pp.str "Your user interface does not support the Ltac debugger.") *)

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
      let open DebugHook.Action in
      match cmd with
      | Ignore -> l ()
      | UpdBpts updates -> upd_bpts updates; l ()
      | GetStack ->
        ((hook)()).submit_answer (Stack (format_stack (get_stack ())));
        l ()
      | GetVars framenum ->
        ((hook)()).submit_answer (Vars (get_vars framenum));
        l ()
      | _ -> action := cmd; cmd
    in
    l ())

end

let defer_output = Comm.defer_output

(* Prints the goal *)

let db_pr_goal gl =
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let concl = Proofview.Goal.concl gl in
  let penv = Termops.Internal.print_named_context env sigma in
  let pc = Printer.pr_econstr_env env sigma concl in
    str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl () ++ fnl ()

let db_pr_goal =
  let open Proofview in
  let open Notations in
  Goal.goals >>= fun gl ->
  Monad.List.map (fun x -> x) gl >>= fun gls ->
  let pg = str (CString.plural (List.length gls) "Goal") ++ str ":" ++ fnl () ++
      Pp.seq (List.map db_pr_goal gls) in
  Proofview.tclLIFT (Comm.goal pg)

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

let print_loc desc loc =
  let open Loc in
  match loc with
  | Some loc ->
    let src = (match loc.fname with
    | InFile {file} -> file
    | ToplevelInput -> "ToplevelInput")
    in
    Printf.sprintf "%s: %s %d/%d %d:%d\n" desc src loc.bp loc.line_nb
      (loc.bp - loc.bol_pos_last) (loc.ep - loc.bol_pos_last)
  | None -> Printf.sprintf "%s: loc is None" desc

let print_loc_tac tac =
  let (desc, loc) = tac_loc tac in
  print_loc desc loc
[@@@ocaml.warning "+32"]

let cvt_stack stack =
  List.map (fun k ->
    let (loc, k) = k in
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
    ) stack

(* Each list entry contains multiple trace frames. *)
let trace_chunks : ltac_trace list ref = ref [([], [])]
let push_chunk trace = trace_chunks := trace :: !trace_chunks
let pop_chunk trace = trace_chunks := List.tl !trace_chunks

let prev_stack = ref (Some [])  (* previous stopping point in debugger *)
let prev_trace_chunks : ltac_trace list ref = ref [([], [])]


let save_loc tac varmap trace =
(*  Comm.print (print_loc_tac tac);*)
  let stack, varmaps = match trace with
    | Some (stack, varmaps) -> stack, varmaps
    | None -> [], []
  in
  debugger_state.cur_loc <- CAst.(tac.loc);
  let (pstack, pvars) = List.fold_right (fun (s,v) (os, ov) -> (s @ os), (v @ ov))
    !trace_chunks ([],[]) in
  debugger_state.stack <- cvt_stack (stack @ pstack);
  debugger_state.varmaps <- varmap :: (varmaps @ pvars)

(* Prints the goal and the command to be executed *)
let goal_com tac varmap trace =
  save_loc tac varmap trace;
  Proofview.tclTHEN
    db_pr_goal
    (if Comm.isTerminal () || debugger_state.cur_loc = None then
      (Proofview.tclLIFT (Comm.output (str "Going to execute:" ++ fnl () ++ prtac tac)))
    else
      Proofview.tclLIFT (Proofview.NonLogical.return ()))

(* [run (new_ref _)] gives us a ref shared among [NonLogical.t]
   expressions. It avoids parameterizing everything over a
   reference. *)
let skipped = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let skip = Proofview.NonLogical.run (Proofview.NonLogical.ref 0)
let idtac_breakpt = Proofview.NonLogical.run (Proofview.NonLogical.ref None)
let idtac_bpt_stop = ref false

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
  if Sys.os_type = "Unix" then
    Sys.set_signal Sys.sigusr1 (Sys.Signal_handle
      (fun _ -> set_break true));
  let open Proofview.NonLogical in
  let x = (skip:=0) >> (skipped:=0) >> (idtac_breakpt:=None) in
  if is_tac then begin
    idtac_bpt_stop.contents <- false;
    make Comm.init >> x
  end else x

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
    Comm.read >>= fun inst ->
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

let at_breakpoint tac =
  let open Loc in
  let check_bpt dirpath offset =
(*    Printf.printf "In tactic_debug, dirpath = %s offset = %d\n%!" dirpath offset;*)
    BPSet.mem { dirpath; offset } !breakpoints
  in
  match CAst.(tac.loc) with
  | Some {fname=InFile {dirpath=Some dirpath}; bp} -> check_bpt dirpath bp
  | Some {fname=ToplevelInput;                 bp} -> check_bpt "Top"   bp
  | _ -> false

[@@@ocaml.warning "-32"]
open Tacexpr

let pr_call_kind n k =
  let (loc, k) = k in
  let kind = (match k with
  | LtacMLCall _ -> "LtacMLCall"
  | LtacNotationCall _ -> "LtacNotationCall"
  | LtacNameCall l ->
    let name = (KerName.to_string l) ^ (print_loc "" loc) in
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
  let stack, varmaps = match trace with
    | Some (stack, varmaps) -> Some stack, Some (varmap :: varmaps)
    | None -> None, Some [varmap] in
  let runprint = print_run_ctr true in
  let open Proofview.NonLogical in
  let (>=) = Proofview.tclBIND in
  (* What to print and to do next *)
  let newlevel =
    Proofview.tclLIFT !skip >= fun s ->
      let stop_here () =
(*        dump_stack "at debug_prompt" stack;*)
(*        dump_varmaps "at debug_prompt" varmaps;*)
        prev_stack.contents <- stack;
        prev_trace_chunks.contents <- trace_chunks.contents;
        Proofview.tclTHEN (goal_com tac varmap trace) (Proofview.tclLIFT (prompt lev))
      in
      let stacks_info stack p_stack =
        (* performance impact? *)
        let st_chunks =  StdList.map (fun (s, _) -> s) trace_chunks.contents in
        let st =      StdList.concat ((Option.default [] stack) :: st_chunks) in
        let prev_st_chunks = StdList.map (fun (s, _) -> s) prev_trace_chunks.contents in
        let st_prev = StdList.concat ((Option.default [] p_stack) :: prev_st_chunks) in
        let l_cur, l_prev = StdList.length st, StdList.length st_prev in
        st, st_prev, l_cur, l_prev
      in
      let p_stack = prev_stack.contents in
      if action.contents = DebugHook.Action.Continue && at_breakpoint tac then
        (* todo: skip := 0 *)
        stop_here ()
      else if get_break () then begin
        set_break false;
        stop_here ()
      end else if s = 1 then begin
        Proofview.tclLIFT ((skip := 0) >> runprint) >=
        (fun () -> stop_here ())
      end else if s > 0 then
        Proofview.tclLIFT ((skip := s-1) >>
          runprint >>
          !skip >>= fun new_skip ->
          (if new_skip = 0 then skipped := 0 else return ()) >>
          return (DebugOn (lev+1)))
      else if idtac_bpt_stop.contents then begin
        idtac_bpt_stop.contents <- false;
        stop_here ()
      end else
        Proofview.tclLIFT !idtac_breakpt >= fun idtac_breakpt ->
          if Option.has_some idtac_breakpt then
            Proofview.tclLIFT(runprint >> return (DebugOn (lev+1)))
          else begin
            let open DebugHook.Action in
            let stop = match action.contents with
              | Continue -> false
              | StepIn   -> true
              | StepOver -> let st, st_prev, l_cur, l_prev = stacks_info stack p_stack in
                            if l_cur = 0 || l_cur < l_prev then true (* stepped out *)
                            else if l_prev = 0 (*&& l_cur > 0*) then false
                            else
                              let peq = StdList.nth st (l_cur - l_prev) == (StdList.hd st_prev) in
                              (l_cur > l_prev && (not peq)) ||  (* stepped out *)
                              (l_cur = l_prev && peq)  (* stepped over *)
              | StepOut  -> let st, st_prev, l_cur, l_prev = stacks_info stack p_stack in
                            if l_cur < l_prev then true
                            else if l_prev = 0 then false
                            else
                              StdList.nth st (l_cur - l_prev) != (StdList.hd st_prev)
              | Skip | RunCnt _ | RunBreakpoint _ -> false (* handled elsewhere *)
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

let is_breakpoint brkname s = match brkname, s with
  | Some s, MsgString s'::_ -> String.equal s s'
  | _ -> false

let db_breakpoint debug s =
  let open Proofview.NonLogical in
  !idtac_breakpt >>= fun opt_breakpoint ->
  match debug with
  | DebugOn lev when not (CList.is_empty s) && is_breakpoint opt_breakpoint s ->
    idtac_bpt_stop.contents <- true;
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
