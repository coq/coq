(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac debugger interface; clients should register hooks to interact
   with their provided interface. *)
module Action = struct
  type t =
    | StepIn
    | StepOver
    | StepOut
    | Continue
    | Skip
    | Interrupt
    | Help
    | RunCnt of int
    | RunBreakpoint of string
    | Command of string
    | Failed
    | Ignore (* do nothing, read another command *)

  (* XXX: Could we move this to the CString utility library? *)
  let possibly_unquote s =
    if String.length s >= 2 && s.[0] == '"' && s.[String.length s - 1] == '"' then
      String.sub s 1 (String.length s - 2)
    else
      s

  let parse_complex inst : (t, string) result =
    if 'r' = String.get inst 0 then
      let arg = String.(trim (sub inst 1 (length inst - 1))) in
      if arg <> "" then
        match int_of_string_opt arg with
        | Some num ->
          if num < 0 then
            Error "number must be positive"
          else
            Ok (RunCnt num)
        | None ->
          Ok (RunBreakpoint (possibly_unquote arg))
      else
        Error ("invalid input: " ^ inst)
    else
      Error ("invalid input: " ^ inst)

  (* XXX: Should be moved to the clients *)
  let parse inst : (t, string) result =
    match inst with
    | ""  -> Ok StepIn
    | "s" -> Ok Skip
    | "x" -> Ok Interrupt
    | "h"| "?" -> Ok Help
    | _ -> parse_complex inst
end

module Answer = struct
  type t =
    | Prompt of Pp.t
    | Goal of Pp.t
    | Output of Pp.t
end

module Intf = struct

  type t =
    { read_cmd : unit -> Action.t
    (** request a debugger command from the client *)
    ; submit_answer : Answer.t -> unit
    (** receive a debugger answer from Ltac *)
    ; isTerminal : bool
    (** whether the debugger is running as a terminal (non-visual) *)
    }

  let ltac_debug_ref : t option ref = ref None
  let set hooks = ltac_debug_ref := Some hooks
  let get () = !ltac_debug_ref

end

(* tactic_debug defines breakpoints in terms of the module dirpath and
   the offset in the source file.  The ide client identifies
   breakpoints by absolute file names of the source file and the offset
   within.  The client doesn't know the module dirpath.

   Users may set breakpoints in files before they have been "Load"ed,
   when their dirpaths are unknown.  To address this, the Load code
   calls refresh_bpts so that such breakpoints can then by seen by tactic_debug.
*)

(* breakpoints as used by tactic_debug *)
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

let check_bpt dirpath offset =
  BPSet.mem { dirpath; offset } !breakpoints

(* breakpoints as defined by the debugger IDE, using absolute file names *)
type ide_breakpoint = {
  file : string;
  offset : int;
}

module IBPSet = CSet.Make(struct
  type t = ide_breakpoint
  let compare b1 b2 =
    let c1 = Int.compare b1.offset b2.offset in
    if c1 <> 0 then c1 else String.compare b1.file b2.file
  end)

(* breakpoints as defined by the debugger IDE, using absolute file names *)
let ide_breakpoints = ref IBPSet.empty

(** add or remove a single breakpoint.  Maps the breakpoint from
  IDE format (absolute path name, offset) to (module dirpath, offset)
  opt - true to add, false to remove
  ide_bpt - the breakpoint (absolute path name, offset)
  *)
let update_bpt opt ide_bpt =
  let open Names in
  let fname = ide_bpt.file in
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
          with _ -> []))
    end
  in
  let dirpath = DirPath.to_string dp in
  let bp = { dirpath; offset=ide_bpt.offset } in
(*  Printf.printf "update_bpt: %s -> %s  %d\n%!" fname dirpath ide_bpt.offset;*)
  match opt with
  | true  -> breakpoints := BPSet.add bp !breakpoints
  | false -> breakpoints := BPSet.remove bp !breakpoints

(** refresh breakpoints, for use when loadpaths are updated, e.g. by the "Load" command *)
let refresh_bpts () =
  breakpoints := BPSet.empty;
  IBPSet.iter (update_bpt true) !ide_breakpoints

(** opt = true to add a breakpoint, false to remove *)
let upd_ide_bpt file offset opt =
  let bp = { file; offset } in
  match opt with
  | true ->
    ide_breakpoints := IBPSet.add bp !ide_breakpoints;  (* todo: error if already set? *)
    update_bpt true bp
  | false ->
    ide_breakpoints := IBPSet.remove bp !ide_breakpoints; (* todo: error if not found? *)
    update_bpt false bp

let forward_get_stack = ref (fun x -> failwith "forward_get_stack")
let forward_get_vars = ref (fun x -> failwith "forward_get_vars")

let break = ref false
(* causes the debugger to stop at the next step *)

let get_break () = !break
let set_break b = break := b
