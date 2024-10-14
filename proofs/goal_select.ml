(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(* spiwack: I'm choosing, for now, to have [goal_selector] be a
   different type than [goal_reference] mostly because if it makes sense
   to print a goal that is out of focus (or already solved) it doesn't
   make sense to apply a tactic to it. Hence it the types may look very
   similar, they do not seem to mean the same thing. *)
type t =
  | SelectAlreadyFocused
  | SelectNth of int
  | SelectList of (int * int) list
  | SelectId of Id.t
  | SelectAll

let pr_range_selector (i, j) =
  if i = j then Pp.int i
  else Pp.(int i ++ str "-" ++ int j)

let pr_goal_selector = let open Pp in function
  | SelectAlreadyFocused -> str "!"
  | SelectAll -> str "all"
  | SelectNth i -> int i
  | SelectList l -> prlist_with_sep pr_comma pr_range_selector l
  | SelectId id -> str "[" ++ Id.print id ++ str "]"

let parse_goal_selector = function
  | "!" -> SelectAlreadyFocused
  | "all" -> SelectAll
  | i ->
      let err_msg = "The default selector must be \"all\", \"!\" or a natural number." in
      begin try
              let i = int_of_string i in
              if i < 0 then CErrors.user_err Pp.(str err_msg);
              SelectNth i
        with Failure _ -> CErrors.user_err Pp.(str err_msg)
      end

(* Default goal selector: selector chosen when a tactic is applied
   without an explicit selector. *)
let { Goptions.get = get_default_goal_selector } =
  Goptions.declare_interpreted_string_option_and_ref
    parse_goal_selector
    (fun v -> Pp.string_of_ppcmds @@ pr_goal_selector v)
    ~key:["Default";"Goal";"Selector"]
    ~value:(SelectNth 1)
    ()

(* Select a subset of the goals *)
let tclSELECT ?nosuchgoal g tac = match g with
  | SelectNth i -> Proofview.tclFOCUS ?nosuchgoal i i tac
  | SelectList l -> Proofview.tclFOCUSLIST ?nosuchgoal l tac
  | SelectId id -> Proofview.tclFOCUSID ?nosuchgoal id tac
  | SelectAll -> tac
  | SelectAlreadyFocused ->
    let open Proofview.Notations in
    Proofview.numgoals >>= fun n ->
    if n == 1 then tac
    else
      let e = CErrors.UserError
          Pp.(str "Expected a single focused goal but " ++
              int n ++ str " goals are focused.")
      in
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info e
