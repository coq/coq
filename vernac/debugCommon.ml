(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open DebuggerTypes

(* tells whether Ltac Debug is set *)
let debug = ref false  (* todo: relation to tacinterp.is_traced *)


(* todo: here? *)
type fmt_stack_f = unit -> string list
type fmt_vars_f = int -> db_vars_rty
type chunk = Loc.t option list * fmt_stack_f * fmt_vars_f

let empty_chunk = [], (fun _ -> []), (fun _ -> [])

(* can some of these go away? *)
let stack_chunks : chunk list ref = ref []
let top_chunk : chunk ref = ref empty_chunk
let cur_loc : Loc.t option ref = ref None


(* Ltac history mechanism *)

type history = {
  stack_chunks : chunk list;
  top_chunk : chunk;
  cur_loc : Loc.t option;
  goals : Proofview.Goal.t list;
}

(* circular buffer *)
let history : history option array ref = ref [| |]

let hist_first = ref 0 (* index of the first (oldest) entry *)
let hist_count = ref 0 (* number of valid entries *)

let cur_goals = ref [] (* current goals *)

(* selects history entry to display; # of steps back in history (0..n),
   0 = current Ltac* state *)
let hist_index = ref 0

let in_history () = !hist_index <> 0

let mod_len n =
  let len = (Array.length !history) in
  let rv = n mod len in
  if rv >= 0 then rv else rv + len

[@@@ocaml.warning "-32"]
let test = (try let _ = Sys.getenv("TEST") in true with _ -> false)
[@@@ocaml.warning "+32"]

(* n is the # of entries before the current stop point to fetch.  0 = use current stop point
 *)
let get_history n =
(*  if test then Printf.eprintf "get_history: n = %d hist_count = %d hist_index = %d\n%!" *)
(*      n !hist_count !hist_index; *)
  if n >= !hist_count || n < 0 then failwith (Printf.sprintf "get_history %d %d" n !hist_count);
    (* todo: or just be silent? *)
  let i = mod_len (!hist_first + !hist_count - 1 - n) in
  match Array.get !history i with
  | Some h -> h
  | None -> failwith "get_history entry is None"

let save_goals () =
  if !debug then begin
    let open Proofview in
    let open Notations in
    (* todo: Goal.goals is not entirely trivial (perf impact?) *)
    Proofview.Goal.goals >>= fun gl ->
    Monad.List.map (fun x -> x) gl >>= fun gls ->
    cur_goals := gls;
    Proofview.tclLIFT (Proofview.NonLogical.return ())
  end else
    Proofview.tclLIFT (Proofview.NonLogical.return ())
  [@@ocaml.warning "-3"]

(* Find the closest prior history entry whose top of stack is the same function call as
   the current entry (or prior to entering that function) AND
   in which the goals differ from the current entry.
   Assume that only "goals" and its sigma can change while in the debugger *)
let get_prev_goalts () =
  let hentry = get_history !hist_index in
  let add gs set =
    List.fold_left (fun s g -> Evar.Set.add (Proofview.Goal.goal g) s) set gs in
  let curr = add hentry.goals Evar.Set.empty in
  let cur_st = List.concat_map (fun (locs,_,_) -> locs)  (hentry.top_chunk :: hentry.stack_chunks) in
  let l_cur = List.length cur_st in
  let eq l1 l2 = List.fold_left2 (fun eq l1 l2 -> eq && (l1==l2)) true l1 l2 in
  let rec loop i =
    if i >= !hist_count then None
    else begin
      let prev_hentry = (get_history i) in
      let prev_st = List.concat_map (fun (locs,_,_) -> locs)  (prev_hentry.top_chunk :: prev_hentry.stack_chunks) in
      let l_prev = List.length prev_st in
      if l_prev > l_cur then
        loop (i+1)
      else if l_prev < l_cur || eq prev_st cur_st then begin
        let prev_goals = (get_history i).goals in
        let prev = add prev_goals Evar.Set.empty in
        if Evar.Set.equal curr prev then
          loop (i+1)
        else
          Some prev_goals
      end else
        loop (i+1)
    end
  in
  if l_cur > 0 then
    loop (!hist_index + 1)
  else None

let history_default = 10
let history_buf_size = ref history_default

let set_history_size n =
  history_buf_size := if n < 0 then 0 else n;
  history := Array.make (n+1) None

let () =
  let open Goptions in
  declare_int_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Ltac";"Debug";"History"];
      optread  = (fun () -> Some !history_buf_size);
      optwrite = (fun n -> set_history_size (Option.default history_default n)) }

let reset_history n =
(*  if test then Printf.eprintf "reset_history %d\n%!" n; *)
(*  if test then Printexc.print_raw_backtrace stderr (Printexc.get_callstack 50); *)
  assert (n >= 0);
  (* allow garbage collection of previous contents *)
  for i = !hist_first to !hist_first + !hist_count do
      Array.set !history (mod_len i) None;
  done;
  hist_first := 0;
  hist_count := 0;
  hist_index := 0

let append_history entry =
  let i = mod_len (!hist_first + !hist_count) in
  Array.set !history i (Some entry);
  if !hist_count < (Array.length !history) then
    incr hist_count
  else
    hist_first := mod_len (!hist_first + 1)
(*  if test then Printf.eprintf "append_history: hist_count = %d hist_first = %d\n%!" !hist_count !hist_first *)

let set_debug b = debug := b

let get_debug () = !debug

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
    if fname = "ToplevelInput" then
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
          with _ -> []))
    end
  in
  let dirpath = DirPath.to_string dp in
  let bp = { dirpath; offset } in
  match opt with
  | true  -> breakpoints := BPSet.add bp !breakpoints
  | false -> breakpoints := BPSet.remove bp !breakpoints

let upd_bpts updates =
  List.iter (fun op ->
    let ((file, offset), opt) = op in
    update_bpt file offset opt;
  ) updates

let check_bpt dirpath offset =
    BPSet.mem { dirpath; offset } !breakpoints

let break = ref false
(* causes the debugger to stop at the next step *)

let print_loc desc loc =
  let open Loc in
  match loc with
  | Some loc ->
    let src = (match loc.fname with
    | InFile {file} -> file
    | ToplevelInput -> "ToplevelInput")
    in
    Printf.sprintf "%s: %s %d:%d/%d %d:%d\n" desc src loc.bp loc.ep loc.line_nb
      (loc.bp - loc.bol_pos) (loc.ep - loc.bol_pos_last)
  | None -> Printf.sprintf "%s: loc is None\n" desc

let breakpoint_stop loc =
  if !break then begin
    break := false;
    true
  end else
    let open Loc in
    match loc with
    | Some {fname=InFile {dirpath=Some dirpath}; bp} -> check_bpt dirpath bp
    | Some {fname=ToplevelInput;                 bp} -> check_bpt "Top"   bp
    | _ -> false


(* stack state for the previous stopping point, used to support StepIn and StepOut *)
let prev_top_chunk : chunk ref = ref empty_chunk
let prev_chunks : chunk list ref = ref []

(* let test = try let _ = Sys.getenv("TEST") in true with _ -> false *)
(* TODO: shouldn't be printing messages during compile, need to check if debug enabled *)

let pop_chunk () =
  if !debug then
    stack_chunks := List.tl !stack_chunks
(*  if test then Printf.eprintf "pop_chunk: num chunks = %d\n%!" (List.length !stack_chunks) *)

let new_stop_point () =
  if !debug then begin
    prev_top_chunk := !top_chunk;
    prev_chunks := !stack_chunks
  end
(*  if test then Printf.eprintf "new_stop_point: num chunks = %d\n%!" (List.length !stack_chunks) *)

let set_top_chunk chunk =
  if !debug then
    top_chunk := chunk

let save_chunk chunk loc =
  if !debug && loc <> None then begin
    top_chunk := chunk;
    cur_loc := loc;
    append_history { stack_chunks=(!stack_chunks); top_chunk=(!top_chunk); cur_loc=(!cur_loc);
        goals=(!cur_goals) }
  end
(*  let (locs,_,_)= chunk in *)
(*  if test then Printf.eprintf "save_chunk: chunk size = %d loc = %s\n%!" (List.length locs) *)
(*    (print_loc "" loc); *)
(*  if test then Printf.eprintf "mem used by buf = %d\n%!" (Obj.reachable_words (Obj.magic history)) *)

let push_top_chunk () =
  if !debug then
    stack_chunks := !top_chunk :: !stack_chunks
(*
   if test then
     let (locs,_,_)= !top_chunk in
       Printf.eprintf "push_top_chunk: size = %d num chunks = %d\n%!"
         (List.length locs) (List.length !stack_chunks)
*)


let action = ref DebugHook.Action.StepOver

let stepping_stop loc =
  if loc = None then false
  else begin
    let locs_info () =
      (* performance impact? *)
      let hentry = get_history !hist_index in
      let st =      List.concat_map (fun (locs,_,_) -> locs)  (hentry.top_chunk :: hentry.stack_chunks) in
      let st_prev = List.concat_map (fun (locs,_,_) -> locs)  (!prev_top_chunk :: !prev_chunks) in
      let l_cur, l_prev = List.length st, List.length st_prev in
      st, st_prev, l_cur, l_prev
    in

    let open DebugHook.Action in
    match !action with
    | ContinueRev
    | Continue -> false
    | StepInRev
    | StepIn   -> true
    | StepOverRev
    | StepOver -> let st, st_prev, l_cur, l_prev = locs_info () in
                  if l_cur = 0 || l_cur < l_prev then true (* stepped out *)
                  else if l_prev = 0 (*&& l_cur > 0*) then false
                  else
                    let peq = List.nth st (l_cur - l_prev) == (List.hd st_prev) in
                    (l_cur > l_prev && (not peq)) ||  (* stepped out *)
                    (l_cur = l_prev && peq)  (* stepped over *)
    | StepOutRev
    | StepOut  -> let st, st_prev, l_cur, l_prev = locs_info () in
                  if l_cur < l_prev then true
                  else if l_prev = 0 then false
                  else
                    List.nth st (l_cur - l_prev) != (List.hd st_prev)
    | Skip | RunCnt _ | RunBreakpoint _ -> false (* not detected here *)
    | _ -> failwith ("invalid stepping action: " ^ (DebugHook.Action.to_string !action))
  end

open Pp (* for str *)

module CSet = CSet.Make (Names.DirPath)
let bad_dirpaths = ref CSet.empty

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
  let items = String.split_on_char '.' text in
  let ilen = List.length items in
  let routine = List.nth items (ilen-1) in
  try
    let open Loc in
      match loc with
      | Some { fname=InFile {dirpath=(Some dp)}; line_nb } ->
        let dplen = String.length dp in
        let lastdot = String.rindex dp '.' in
        let file = String.sub dp (lastdot+1) (dplen - (lastdot + 1)) in
        let path = String.sub dp 0 lastdot in
        Printf.sprintf "%s:%d, %s  (%s)" routine line_nb file path
      | Some { fname=ToplevelInput; line_nb } ->
        if ilen > 1 then
          Printf.sprintf "%s:%d, %s" routine line_nb (List.hd items)
        else
          Printf.sprintf "%s:%d" routine line_nb
      | _ -> text
  with _ -> text


let format_stack s locs =
  List.rev (
    List.rev_map2 (fun tac loc ->
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
      ) s locs
    )

(* end dependencies *)


(* Comm module *)
[@@@ocaml.warning "-32"]
let hook () = Option.get (DebugHook.Intf.get ())
let wrap = Proofview.NonLogical.make

(* TODO: ideally we would check that the debugger hooks are
   correctly set, however we don't do this yet as debugger
   initialization is unconditionally done for example in coqc.
   Improving this would require some tweaks in tacinterp which
   are out of scope for the current refactoring. *)
let init () =
  if !debug then begin
    if Sys.os_type = "Unix" then
      Sys.set_signal Sys.sigusr1 (Sys.Signal_handle
        (fun _ -> break := true));
    stack_chunks := [];
    prev_chunks := [];
    top_chunk := empty_chunk;
    prev_top_chunk := empty_chunk;
    cur_goals := [];
    cur_loc := None;
    reset_history !history_buf_size;
    let open DebugHook in
    match Intf.get () with
    | Some intf ->
      if Intf.(intf.isTerminal) then
        action := Action.StepIn
      else begin
        break := false;
        breakpoints := BPSet.empty;
        (hook ()).Intf.submit_answer (Answer.Init);
        while
          let cmd = (hook ()).Intf.read_cmd true in
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
  end

open DebugHook.Intf
open DebugHook.Answer

let prompt p = wrap (fun () -> (hook ()).submit_answer (Prompt p))
let output o = wrap (fun () -> (hook ()).submit_answer (Output o))

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

let print g = (hook ()).submit_answer (Output (str g))

let get_all_chunks () =
  if !hist_count = 0 then [] else
    let hist = get_history !hist_index in
    hist.top_chunk :: hist.stack_chunks

let fmt_stack () =
  let full = get_all_chunks () in
  let cur_loc = (get_history !hist_index).cur_loc in
  let common = List.concat_map (fun (_, fmt_stackL, _) -> fmt_stackL ()) full in
  let locs = cur_loc :: List.concat_map (fun (locs, _, _) -> locs) full in
  let common = List.map (fun i -> Some i) common in
  format_stack (common @ [None]) locs

let get_vars framenum =
  let rec get_chunk chunks framenum =
    match chunks with
    | [] -> []
    | (locs, _, get_vars) :: tl ->
      let len = List.length locs in
      if len <= framenum then
        get_chunk tl (framenum - len)
      else
        get_vars framenum
  in
  get_chunk (get_all_chunks ()) framenum

let db_fmt_goal gl =
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let penv = Termops.Internal.print_named_context env in
  let pc = Printer.pr_econstr_env env (Tacmach.project gl) concl in
    str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl () ++ fnl ()

let db_fmt_goals () =
  let gls = (get_history !hist_index).goals in
  (* todo: say "No more goals"?  What if they are shelved?  Same behavior in Ltac1 *)
  str (CString.plural (List.length gls) "Goal") ++ str ":" ++ fnl () ++
      Pp.seq (List.map db_fmt_goal gls)

let isTerminal () = (hook ()).isTerminal

let db_pr_goals () =  (* todo: drop the "db_" prefix *)
  if isTerminal () then
    (hook ()).submit_answer (Output (db_fmt_goals ()))

let db_pr_goals_t = (* todo: try to get rid of this version *)
(*  Printf.eprintf "db_pr_goals_t\n%!"; *)
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> db_pr_goals ()))

let goalt_to_evd goals =
  let open Proofview in
  let sigma = match goals with
    | hd :: tl -> Goal.sigma hd
    | [] -> Evd.empty
  in
  let goals = List.map (fun gl -> Goal.goal gl) goals in (* "compatibility: avoid" *)
  (sigma, goals)

type export_goals_args = {
  sigma:    Evd.evar_map;
  goals:    Evar.t list;
  bgsigma:  Evd.evar_map;
  stack:    (Evar.t list * Evar.t list) list;
  show_diffs: bool;
}

let fwd_db_subgoals = (ref ((fun x y -> failwith "fwd_db_subgoals")
                  : goal_flags -> export_goals_args option ->
                    Proof_diffs.goal_map_args option ->
                    subgoals_rty))

(* get arguments for printing goals, either current or from history
   and set up to show diffs *)
let args_to_print_goals () =
  let ngoalts = (get_history !hist_index).goals in
  let nsigma, nall_goals = goalt_to_evd ngoalts in
  let pf = Vernacstate.Declare.give_me_the_proof () in  (* todo what if no proof? *)
  let p = Proof.data pf in
  let osigma, oall_goals = match get_prev_goalts () with
  | Some ogoalts -> goalt_to_evd ogoalts
  | None -> nsigma (* not used *), []
  in
  let export_goals_args = Some {
    sigma=nsigma;
    goals=nall_goals;
    bgsigma=p.sigma;
    stack=p.stack;
    show_diffs=(oall_goals <> []);
  } in
  let goal_map_args =
    match ngoalts with
    | [] -> None
    | goalt :: _ ->
      let nhas_fg_goals = true(* ??? *) in
      let env = Proofview.Goal.env goalt in
      Some Proof_diffs.{
        oall_goals=(Evar.Set.of_list oall_goals);
        nall_goals=(Evar.Set.of_list nall_goals);
        osigma;
        nsigma;
        oto_constr= (fun () -> Proof_diffs.to_constr2 env osigma oall_goals pf);
        nto_constr= (fun () -> Proof_diffs.to_constr2 env nsigma nall_goals pf);
        nhas_fg_goals
      }
  in
  export_goals_args, goal_map_args
  [@@ocaml.warning "-3"]

let read () =
  let rec l () =
    let cmd = (hook ()).read_cmd true in
    action := cmd;  (* todo: issue being here, don't want to lose initial setting??? *)
(*    Printf.eprintf "\naction = %s\n%!" (DebugHook.Action.to_string cmd); *)
    let open DebugHook.Action in
    (* handle operations that don't change Ltac* or history state *)
    begin match cmd with
      | Ignore -> l ()
      | UpdBpts updates -> upd_bpts updates; l ()
      | GetStack ->
        (hook ()).submit_answer (Stack (fmt_stack ()));
        l ()
      | GetVars framenum ->
        (hook ()).submit_answer (Vars (get_vars framenum));
        l ()
      | Subgoals flags ->
        let export_goals_args, goal_map_args = args_to_print_goals () in
        (hook ()).submit_answer (Subgoals (!fwd_db_subgoals flags export_goals_args goal_map_args));
        l ()
      | StepIn | StepOver | StepOut | Continue -> hist_loop (-1) (* forwards *)
      | StepInRev | StepOverRev | StepOutRev | ContinueRev -> hist_loop 1 (* backwards *)
      | _ -> ()
    end

  and hist_loop incr =    (* step through history *)
    let do_stop () =
      let msg = tag "message.prompt"
            @@ fnl () ++ str (Printf.sprintf "History (%d) > "(-(!hist_index))) in
      (hook ()).submit_answer (Prompt msg);
      l ()
    in

(*    Printf.eprintf "hist_loop: incr = %d hist_index = %d hist_count = %d\n%!" *)
(*      incr !hist_index !hist_count; *)
    if incr = 1 && !hist_index+1 = !hist_count then begin
(*      Printf.eprintf "hist_loop: hist_count = %d hist_index = %d\n%!" !hist_index !hist_count; *)
      Feedback.msg_info Pp.(str "No more history available");
      do_stop ();
    end else if incr = 1 || !hist_index > 0 then begin
      hist_index := !hist_index + incr;  (* assert >= 0? *)
(*      Printf.eprintf "hist_index set to %d\n%!" !hist_index; *)
      let hentry = get_history !hist_index in
      let loc = hentry.cur_loc in
      if breakpoint_stop loc || stepping_stop loc then begin
        (* stop in history *)
        prev_top_chunk := hentry.top_chunk;
        prev_chunks := hentry.stack_chunks;
        do_stop ();
      end else
        hist_loop incr
    end
    (* else fall through, take step(s) in Ltac* *)
  in
  l ();
  !action

(* compare to CErrors.noncritical *)
let is_showable_exn = function
  | Sys.Break -> false
  | _ -> true

let show_exn_in_debugger exn =
  let exn0, info = exn in
  let stack_len = 1 + (List.fold_left (fun len (locs, _, _) -> List.length locs + len) 
    0 (get_all_chunks ())) in 
  if not (isTerminal ()) && is_showable_exn exn0 &&
    (stack_len > 1) &&  (* don't stop in "tac1; tac2." *) 
    !hist_count > 0 (* skip single tactic, e.g. "fail." *) then begin
    let open Pp in

    (hook ()).submit_answer (Output (tag "message.red" @@ (CErrors.iprint exn) ++ fnl () ++
      str "Step forward to exit the debugger"));
    (hook ()).submit_answer (Prompt (tag "message.prompt" @@ fnl () ++ str "TcDebug > "));
    ignore @@ read()
  end
