(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type proof_node = {
        (* In saw mode, identation depends directly from
         * the remaining subgoals to be proven
         * *)
        remaining_subgoals : int;
        (* A subgoal stack is a list of remaining subgoals
         * at each "keypoint";
         *
         * Imagine you have to solve a subgoal "S", and you
         * know that "n" subgoals remain to be proved.
         *
         * After running a tactic, let us call "m" the number of
         * remaining subgoals to be proven; 3 cases occur:
         * - if "m" > "n", then you know that you have entered a
         *   new indentation level and that you will close it
         *   once the remaining goals are below "n", so
         *   we push "n" in this case to keep track of it
         * - if "m" = "n" then nothing changes
         * - if "m" < "n" then according to the first case we
         *   have to look if the top of our stack is below "n";
         *   if so we pop our stack, so that our indentation
         *   level is always equal to depth of our stack
         * *)
        subgoals_stack : int list;
        (* [first_step] means that the number of remaining
         * subgoals has changed (cases 1 and 3 of previous enumeration)
         * *)
        first_step : bool;
}
type interp_node = {
  opened_sections : int;
  opened_modules : int;
  interp_mode : proof_node option;
}

(* In the first step, we have not yet any interp node,
 * but we need one to use [compute_interp_node],
 * so we provide one
 * *)
let first_interp_node = {
  opened_sections = 0;
  opened_modules = 0;
  interp_mode = None;
}

(* this functions finds how many modules and sections are opened *)
let get_opened lstk =
  let rec get_opened lstk (sections, modules) =
    match lstk with
    | [] -> (sections, modules)
    | (_, node)::lstk -> get_opened lstk
          ( match node with
            | Lib.OpenedModule(_,_,_)
            | Lib.OpenedModtype(_,_) ->
              sections, 1+modules
            | Lib.OpenedSection(_,_) ->
              1+sections, modules
(*            | Lib.ClosedModule(_)
            | Lib.ClosedModtype(_) ->
              sections, modules-1
            | Lib.ClosedSection(_) ->
              sections-1, modules*)
            | _ -> sections, modules
          )
  in
  match lstk with
  | Ide_blob.Fail(_,_) -> (0,0)
  | Ide_blob.Good lstk -> get_opened lstk (0, 0)

(* given the current pftreestate
 * (or None if we are neither in proof nor tactic mode)
 *  and the previous proof_node, we can compute the
 * current proof_node
 * *)
let compute_interp_node pftso pno lstk =
  let (i_mode, o_msg) =
  match pftso with
  | Ide_blob.Fail(_,_) -> (None, None)
  | Ide_blob.Good (Ide_blob.Message s) -> (None, None)
  | Ide_blob.Good (Ide_blob.Goals goals) ->
     (* we need the number of remaining subgoals in tactic mode *)
     let rs = List.length goals in
     (* and the indication that the proof is really terminated in case
      * rs = 0 for declarative mode
      * *)
     if rs = 0
     then (None, None)
     else
       let (fs, (ss, e_msg)) =
         match pno.interp_mode with
         | None -> (true, ([], None))
         | Some pn ->
            let (fs, (ss, e_msg)) =
             if rs = pn.remaining_subgoals
             then (false, (pn.subgoals_stack, None))
             else (true,
                   if rs > pn.remaining_subgoals
                   then (pn.remaining_subgoals::pn.subgoals_stack, None)
                   else let rec unhead l = match l with
                                           | [] -> ([], Some("Indentation system broken"))
                                           |h::t-> if h = pn.remaining_subgoals
                                                   then unhead t
                                                   else (h::t, None)
                        in unhead pn.subgoals_stack)
            in (fs, (ss, e_msg))
          in
          (Some { remaining_subgoals = rs;
                  subgoals_stack = ss;
                  first_step = fs;
                },
           e_msg)
     in
     let (s, m) = get_opened lstk in
     { opened_sections = s;
       opened_modules = m;
       interp_mode = i_mode;
     }, o_msg

type nesting = {
        module_levels : int;  (* number of opened modules *)
        section_levels : int; (* number of opened sections *)
        subgoal_levels : int; (* number of remaining subgoals *)
        tactic_levels : int;  (* number of imbricated proofs *)
        tactic_alinea : bool; (* are we entering a new node? *)
}

let compute_nesting pno =
  let subgoals, tactic_depth, alinea =
      match pno.interp_mode with
        | None -> (0, 0, true)
        | Some pn -> (pn.remaining_subgoals,
                      List.length pn.subgoals_stack,
                      pn.first_step)
    in
    { section_levels = pno.opened_sections;
      module_levels = pno.opened_modules;
      subgoal_levels = subgoals;
      tactic_levels = tactic_depth;
      tactic_alinea = alinea;
    }
