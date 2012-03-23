(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Vernacexpr

(** Command history stack

    We maintain a stack of the past states of the system. Each
    successfully interpreted command adds an [info] element
    to this stack, storing what were the (label / current proof / ...)
    just _after_ the interpretation of this command.

    - A label is just an integer, starting from Lib.first_command_label
      initially, and incremented at each new successful command.
    - If some proofs are opened, we have their number in [nproofs],
      the name of the current proof in [prfname], the current depth in
      [prfdepth].
    - Otherwise, [nproofs = 0], [prfname = None], [prfdepth = 0]
    - The text of the command is stored (for Show Script currently).
    - A command can be tagged later as non-"reachable" when the current proof
      at the time of this command has been ended by Qed/Abort/Restart,
      meaning we can't backtrack there.
*)

type info = {
  label : int;
  nproofs : int;
  prfname : identifier option;
  prfdepth : int;
  cmd : vernac_expr;
  mutable reachable : bool;
}

let history : info Stack.t = Stack.create ()

(** For debug purpose, a dump of the history *)

let dump_history () =
  let l = ref [] in
  Stack.iter (fun i -> l:=i::!l) history;
  !l

(** Basic manipulation of the command history stack *)

exception Invalid

let pop () = ignore (Stack.pop history)

let npop n =
 (* Since our history stack always contains an initial entry,
    it's invalid to try to completely empty it *)
 if n < 0 || n >= Stack.length history then raise Invalid
 else for i = 1 to n do pop () done

let top () =
  try Stack.top history with Stack.Empty -> raise Invalid

(** Search the history stack for a suitable location. We perform first
    a non-destructive search: in case of search failure, the stack is
    unchanged. *)

exception Found of info

let search test =
  try
    Stack.iter (fun i -> if test i then raise (Found i)) history;
    raise Invalid
  with Found i ->
    while i != Stack.top history do pop () done

(** Register the end of a command and store the current state *)

let mark_command ast =
  Lib.add_frozen_state();
  Lib.mark_end_of_command();
  Stack.push
    { label = Lib.current_command_label ();
      nproofs = List.length (Pfedit.get_all_proof_names ());
      prfname = (try Some (Pfedit.get_current_proof_name ()) with _ -> None);
      prfdepth = max 0 (Pfedit.current_proof_depth ());
      reachable = true;
      cmd = ast }
    history

(** Backtrack by aborting [naborts] proofs, then setting proof-depth back to
    [pnum] and finally going to state number [snum]. *)

let raw_backtrack snum pnum naborts =
  for i = 1 to naborts do Pfedit.delete_current_proof () done;
  Pfedit.undo_todepth pnum;
  Lib.reset_label snum

(** Re-sync the state of the system (label, proofs) with the top
    of the history stack. We may end on some earlier state to avoid
    re-opening proofs. This function will return the final label
    and the number of extra backtracking steps performed. *)

let sync nb_opened_proofs =
  (* Backtrack by enough additional steps to avoid re-opening proofs.
     Typically, when a Qed has been crossed, we backtrack to the proof start.
     NB: We cannot reach the empty stack, since the first entry in the
     stack has no opened proofs and is tagged as reachable.
  *)
  let extra = ref 0 in
  while not (top()).reachable do incr extra; pop () done;
  let target = top ()
  in
  (* Now the opened proofs at target is a subset of the opened proofs before
     the backtrack, we simply abort the extra proofs (if any).
     NB: It is critical here that proofs are nested in a regular way
     (i.e. no more Resume or Suspend commands as earlier). This way, we can
     simply count the extra proofs to abort instead of taking care of their
     names.
  *)
  let naborts = nb_opened_proofs - target.nproofs in
  (* We are now ready to do a low-level backtrack *)
  raw_backtrack target.label target.prfdepth naborts;
  (target.label, !extra)

(** Backtracking by a certain number of (non-state-preserving) commands.
    This is used by Coqide.
    It may actually undo more commands than asked : for instance instead
    of jumping back in the middle of a finished proof, we jump back before
    this proof. The number of extra backtracked command is returned at
    the end. *)

let back count =
  if count = 0 then 0
  else
    let nb_opened_proofs = List.length (Pfedit.get_all_proof_names ()) in
    npop count;
    snd (sync nb_opened_proofs)

(** Backtracking to a certain state number, and reset proofs accordingly.
    We may end on some earlier state if needed to avoid re-opening proofs.
    Return the final state number. *)

let backto snum =
  if snum = Lib.current_command_label () then snum
  else
    let nb_opened_proofs = List.length (Pfedit.get_all_proof_names ()) in
    search (fun i -> i.label = snum);
    fst (sync nb_opened_proofs)

(** Old [Backtrack] code with corresponding update of the history stack.
    [Backtrack] is now deprecated (in favor of [BackTo]) but is kept for
    compatibility with ProofGeneral. It's completely up to ProofGeneral
    to decide where to go and how to adapt proofs. Note that the choices
    of ProofGeneral are currently not always perfect (for instance when
    backtracking an Undo). *)

let backtrack snum pnum naborts =
  raw_backtrack snum pnum naborts;
  search (fun i -> i.label = snum)

(** [reset_initial] resets the system and clears the command history
    stack, only pushing back the initial entry. It should be equivalent
    to [backto Lib.first_command_label], but sligthly more efficient. *)

let reset_initial () =
  let init_label = Lib.first_command_label in
  if Lib.current_command_label () = init_label then ()
  else begin
    if Pfedit.refining() then Pfedit.delete_all_proofs ();
    Lib.reset_label init_label;
    Stack.clear history;
    Stack.push
      { label = init_label;
	nproofs = 0;
	prfname = None;
	prfdepth = 0;
	reachable = true;
	cmd = VernacNop }
      history
  end

(** Reset to the last known state just before defining [id] *)

let reset_name id =
  let lbl =
    try Lib.label_before_name id with Not_found -> raise Invalid
  in
  ignore (backto lbl)

(** When a proof is ended (via either Qed/Admitted/Restart/Abort),
    old proof steps should be marked differently to avoid jumping back
    to them:
     - either this proof isn't there anymore in the proof engine
     - either it's there but it's a more recent attempt after a Restart,
       so we shouldn't mix the two.
    We also mark as unreachable the proof steps cancelled via a Undo. *)

let mark_unreachable ?(after=0) prf_lst =
  let fix i = match i.prfname with
    | None -> raise Not_found (* stop hacking the history outside of proofs *)
    | Some p ->
      if List.mem p prf_lst && i.prfdepth > after
      then i.reachable <- false
  in
  try Stack.iter fix history with Not_found -> ()

(** Parse the history stack for printing the script of a proof *)

let get_script prf =
  let script = ref [] in
  let select i = match i.prfname with
    | None -> raise Not_found
    | Some p when p=prf && i.reachable -> script := i :: !script
    | _ -> ()
  in
  (try Stack.iter select history with Not_found -> ());
  (* Get rid of intermediate commands which don't grow the depth *)
  let rec filter n = function
    | [] -> []
    | {prfdepth=d; cmd=c}::l when n < d -> c :: filter d l
    | {prfdepth=d}::l -> filter d l
  in
  (* initial proof depth (after entering the lemma statement) is 1 *)
  filter 1 !script
