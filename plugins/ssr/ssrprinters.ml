(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Pp
open Names

open Ssrast

let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep

let pp_concat hd ?(sep=str", ") = function [] -> hd | x :: xs ->
  hd ++ List.fold_left (fun acc x -> acc ++ sep ++ x) x xs

(* Term printing utilities functions for deciding bracketing.  *)
let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")
(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term kind s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> kind = Ssrmatching_plugin.Ssrmatching.InParens

(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let pr_guarded guard prc c =
  pp_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c

let with_global_env_evm f x =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  f env sigma x

let prl_constr_expr = with_global_env_evm Ppconstr.pr_lconstr_expr
let pr_glob_constr = with_global_env_evm Printer.pr_glob_constr_env
let prl_glob_constr = with_global_env_evm Printer.pr_lglob_constr_env
let pr_glob_constr_and_expr = function
  | _, Some c -> with_global_env_evm Ppconstr.pr_constr_expr c
  | c, None -> pr_glob_constr c
let pr_term (k, c) = pr_guarded (guard_term k) pr_glob_constr_and_expr c

let pr_hyp (SsrHyp (_, id)) = Id.print id
let pr_hyps = pr_list pr_spc pr_hyp

let pr_occ = function
  | Some (true, occ) ->
    if CList.is_empty occ then mt () else str "{-" ++ pr_list pr_spc int occ ++ str "}"
  | Some (false, occ) ->
    if CList.is_empty occ then mt () else str "{+" ++ pr_list pr_spc int occ ++ str "}"
  | None -> str "{}"

let pr_clear_ne clr =
  if CList.is_empty clr then mt () else str "{" ++ pr_hyps clr ++ str "}"
let pr_clear sep clr = sep () ++ pr_clear_ne clr

let pr_dir = function L2R -> str "->" | R2L -> str "<-"

let pr_simpl = function
  | Simpl -1 -> str "/="
  | Cut -1 -> str "//"
  | Simpl n -> str "/" ++ int n ++ str "="
  | Cut n -> str "/" ++ int n ++ str"/"
  | SimplCut (-1,-1) -> str "//="
  | SimplCut (n,-1) -> str "/" ++ int n ++ str "/="
  | SimplCut (-1,n) -> str "//" ++ int n ++ str "="
  | SimplCut (n,m) -> str "/" ++ int n ++ str "/" ++ int m ++ str "="
  | Nop -> mt ()

(* New terms *)

let pr_ast_closure_term { body } =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Ppconstr.pr_constr_expr env sigma body

let pr_view2 = pr_list mt (fun c -> str "/" ++ pr_ast_closure_term c)

let rec pr_ipat p =
  match p with
  | IPatId id -> Id.print id
  | IPatSimpl sim -> pr_simpl sim
  | IPatClear clr -> pr_clear mt clr
  | IPatCase (Regular iorpat) -> hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")
  | IPatCase (Block m) -> hov 1 (str"[" ++ pr_block m ++ str"]")
  | IPatDispatch(Regular iorpat) -> hov 1 (str "(" ++ pr_iorpat iorpat ++ str ")")
  | IPatDispatch (Block m) -> hov 1 (str"(" ++ pr_block m ++ str")")
  | IPatInj iorpat -> hov 1 (str "[=" ++ pr_iorpat iorpat ++ str "]")
  | IPatRewrite (occ, dir) -> pr_occ occ ++ pr_dir dir
  | IPatAnon All -> str "*"
  | IPatAnon Drop -> str "_"
  | IPatAnon (One _) -> str "?"
  | IPatView v -> pr_view2 v
  | IPatAnon Temporary -> str "+"
  | IPatNoop -> str "-"
  | IPatAbstractVars l -> str "[:" ++ pr_list spc Id.print l ++ str "]"
  | IPatFastNondep -> str">"
and pr_ipats ipats = pr_list spc pr_ipat ipats
and pr_iorpat iorpat = pr_list pr_bar pr_ipats iorpat
and pr_block = function (Prefix id) -> str"^" ++ Id.print id
                      | (SuffixId id) -> str"^~" ++ Id.print id
                      | (SuffixNum n) -> str"^~" ++ int n

let debug_ssr = CDebug.create ~name:"ssreflect" ()
