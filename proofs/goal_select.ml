(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(* Default goal selector: selector chosen when a tactic is applied
   without an explicit selector. *)
let default_goal_selector = ref (SelectNth 1)
let get_default_goal_selector () = !default_goal_selector

let pr_range_selector (i, j) =
  if i = j then Pp.int i
  else Pp.(int i ++ str "-" ++ int j)

let pr_goal_selector = function
  | SelectAlreadyFocused -> Pp.str "!"
  | SelectAll -> Pp.str "all"
  | SelectNth i -> Pp.int i
  | SelectList l ->
    Pp.(str "["
     ++ prlist_with_sep pr_comma pr_range_selector l
     ++ str "]")
  | SelectId id -> Names.Id.print id

let parse_goal_selector = function
  | "!" -> SelectAlreadyFocused
  | "all" -> SelectAll
  | i ->
      let err_msg = "The default selector must be \"all\" or a natural number." in
      begin try
              let i = int_of_string i in
              if i < 0 then CErrors.user_err Pp.(str err_msg);
              SelectNth i
        with Failure _ -> CErrors.user_err Pp.(str err_msg)
      end

let _ = let open Goptions in
  declare_string_option
    { optdepr = false;
      optname = "default goal selector" ;
      optkey  = ["Default";"Goal";"Selector"] ;
      optread = begin fun () ->
        Pp.string_of_ppcmds
          (pr_goal_selector !default_goal_selector)
      end;
      optwrite = begin fun n ->
        default_goal_selector := parse_goal_selector n
      end
    }
