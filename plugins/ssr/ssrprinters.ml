(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Pp
open Names
open Printer
open Tacmach

open Ssrmatching_plugin
open Ssrast

let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep

let pp_concat hd ?(sep=str", ") = function [] -> hd | x :: xs ->
  hd ++ List.fold_left (fun acc x -> acc ++ sep ++ x) x xs

let pp_term gl t =
  let t = Reductionops.nf_evar (project gl) t in pr_econstr t

(* FIXME *)
(* terms are pre constr, the kind is parsing/printing flag to distinguish
 * between x, @x and (x). It affects automatic clear and let-in preservation.
 * Cpattern is a temporary flag that becomes InParens ASAP. *)
(* type ssrtermkind = InParens | WithAt | NoFlag | Cpattern *)
let xInParens = '('
let xWithAt = '@'
let xNoFlag = ' '
let xCpattern = 'x'

(* Term printing utilities functions for deciding bracketing.  *)
let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")
(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term ch1 s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> ch1 = xInParens

(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let pr_guarded guard prc c =
  pp_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c

let prl_constr_expr = Ppconstr.pr_lconstr_expr
let pr_glob_constr c = Printer.pr_glob_constr_env (Global.env ()) c
let prl_glob_constr c = Printer.pr_lglob_constr_env (Global.env ()) c
let pr_glob_constr_and_expr = function
  | _, Some c -> Ppconstr.pr_constr_expr c
  | c, None -> pr_glob_constr c
let pr_term (k, c) = pr_guarded (guard_term k) pr_glob_constr_and_expr c

let pr_hyp (SsrHyp (_, id)) = Id.print id

let pr_occ = function
  | Some (true, occ) -> str "{-" ++ pr_list pr_spc int occ ++ str "}"
  | Some (false, occ) -> str "{+" ++ pr_list pr_spc int occ ++ str "}"
  | None -> str "{}"

(* 0 cost pp function. Active only if Debug Ssreflect is Set *)
let ppdebug_ref = ref (fun _ -> ())
let ssr_pp s = Feedback.msg_debug (str"SSR: "++Lazy.force s)
let _ =
  Goptions.declare_bool_option
    { Goptions.optname  = "ssreflect debugging";
      Goptions.optkey   = ["Debug";"Ssreflect"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !ppdebug_ref == ssr_pp);
      Goptions.optwrite = (fun b -> 
        Ssrmatching.debug b;
        if b then ppdebug_ref := ssr_pp else ppdebug_ref := fun _ -> ()) }
let ppdebug s = !ppdebug_ref s
