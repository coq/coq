(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

let pr = print_string
let pnl = print_newline
let prl = print_endline
let pri = print_int
let prch = print_char

let propt pr_fun = function
  | Some x -> pr "Some "; pr_fun x
  | _ -> pr "None"

let prlist pr_fun sep =
  let rec prlist' = function
    | x::l -> pr_fun x; List.iter pr_sep l
    | _ -> ()
  and pr_sep x = pr sep; pr_fun x
  in prlist'

let level = ref 0
let stack = ref []
let traced = ref []

let init() = level := 0; stack := []

let trace l = traced := l @ !traced
let untrace l = traced := List.filter (fun x -> not (List.mem x l)) !traced
let untrace_all() = traced := []

let mk_str i = String.make i ' '
let tab = ref (Array.init 80 mk_str)

let prtab() = print_string !tab.(!level)

let push s =
  stack := s :: !stack;
  incr level;
  if !level > Array.length !tab then tab := Array.init (2 * !level) mk_str

let pop() =
  if !level > 0 then (
    decr level;
    match !stack with
      | s::l -> stack := l; s
      | _ -> "anomaly in lib/debug"
  ) else "anomaly in lib/debug"

let line = String.make 80 '_'

let enter s =
  if List.mem s !traced then (
    if !level = 0 then prl line;
    prtab(); push s; pr s; prl " begin"
  )

let enter_pr s pr_fun x =
  if List.mem s !traced then (
    if !level = 0 then prl line;
    prtab(); push s; pr s; pr " <- "; pr_fun x; pnl()
  )

let leave s x =
  if List.mem s !traced then (
    let s = pop() in prtab(); pr s; prl " end"; x
  ) else x

let leave_pr s pr_fun x =
  if List.mem s !traced then (
    let s = pop() in prtab(); pr s; pr " -> "; pr_fun x; pnl(); x
  ) else x

let branch s t =
  if List.mem s !traced then (
    prtab(); prl t
  )

let branch_pr s t pr_fun x =
  if List.mem s !traced then (
    prtab();
    if s <> "" then (pr t; prch ' ');
    pr_fun x; pnl()
  )
