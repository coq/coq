(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Term
open Declarations

let pr = print_string
let pnl = print_newline
let prl = print_endline
let pri = print_int
let prch = print_char

let pr_list pr_fun sep =
  let rec prl = function
    | x::l -> pr_fun x; List.iter pr_sep l
    | _ -> ()
  and pr_sep x = pr sep; pr_fun x
  in prl

let pr_ind imap (kn,i) =
  try let ind = (KNmap.find kn imap).mind_packets.(i) in
    pr (string_of_id ind.mind_typename)
  with Not_found -> prn kn

let pr_construct imap ((kn,i),n) =
  try let ind = (KNmap.find kn imap).mind_packets.(i) in
    pr (string_of_id ind.mind_consnames.(n-1))
  with Not_found -> pr "constr:"; prn kn; prch ':'; pri n

let pr_fix ((_,i),(vn,_,_)) = pr_name vn.(i)

let pr_cofix (i,(vn,_,_)) = pr_name vn.(i)

let prc imap =
  let rec prc_rec c =
    match kind_of_term c with
      | App (f,va) ->
	  if Array.length va = 0 then prc_rec f
	  else prch '('; prc_rec f; Array.iter pr_sep va; prch ')'
      | Const kn -> pr (string_of_label (label kn))
      | Construct c -> pr_construct imap c
      | Rel i -> prch 'x'; pri i
      | Prod (n,t,b) -> prch '('; pr_name n; prch ':';
	  prc_rec t; prch ')'; prc_rec b
      | Lambda (n,t,b) -> prch '['; pr_name n; prch ':';
	  prc_rec t; prch ']'; prc_rec b
      | Fix f -> pr_fix f
      | CoFix cf -> pr_cofix cf
      | Ind ind -> pr_ind imap ind
      | Var id -> pr (string_of_id id)
      | _ -> prch '?'
  and pr_sep c = prch ' '; prc_rec c
  in prc_rec

let prv imap va =
  let pr_elt i c = if i>0 then pr ", "; prc imap c in
    if Array.length va = 0 then pr "<empty>"
    else Array.iteri pr_elt va

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
      | _ -> "anomaly"
  ) else "anomaly"

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
