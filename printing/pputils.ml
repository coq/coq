(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Genarg
open Locus
open Genredexpr

let beautify_comments = ref []

let rec split_comments comacc acc pos = function
  | [] -> beautify_comments := List.rev acc; comacc
  | ((b,e),c as com)::coms ->
      (* Take all comments that terminates before pos, or begin exactly
         at pos (used to print comments attached after an expression) *)
      if e<=pos || pos=b then split_comments (c::comacc) acc pos coms
      else split_comments comacc (com::acc) pos coms

let extract_comments pos = split_comments [] [] pos !beautify_comments

let pr_located pr (loc, x) =
  match loc with
  | Some loc when !Flags.beautify ->
    let (b, e) = Loc.unloc loc in
    (* Side-effect: order matters *)
    let before = Pp.comment (extract_comments b) in
    let x = pr x in
    let after = Pp.comment (extract_comments e) in
    before ++ x ++ after
  | _ -> pr x

let pr_ast pr { CAst.loc; v } = pr_located pr (loc, v)

let pr_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar {CAst.v=s} -> Names.Id.print s

let pr_with_occurrences pr keyword (occs,c) =
  match occs with
    | AllOccurrences ->
      pr c
    | NoOccurrences ->
      failwith "pr_with_occurrences: no occurrences"
    | OnlyOccurrences nl ->
      hov 1 (pr c ++ spc () ++ keyword "at" ++ spc () ++
                hov 0 (prlist_with_sep spc (pr_or_var int) nl))
    | AllOccurrencesBut nl ->
      hov 1 (pr c ++ spc () ++ keyword "at" ++ str" - " ++
                hov 0 (prlist_with_sep spc (pr_or_var int) nl))

exception ComplexRedFlag

let pr_short_red_flag pr r =
  if not r.rBeta ||  not r.rMatch || not r.rFix || not r.rCofix || not r.rZeta then
    raise ComplexRedFlag
  else if List.is_empty r.rConst then
    if r.rDelta then mt () else raise ComplexRedFlag
  else (if r.rDelta then str "-" else mt ()) ++
          hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]")

let pr_red_flag pr r =
  try pr_short_red_flag pr r
  with ComplexRedFlag ->
    (if r.rBeta then pr_arg str "beta" else mt ()) ++
      (if r.rMatch && r.rFix && r.rCofix then pr_arg str "iota" else
          (if r.rMatch then pr_arg str "match" else mt ()) ++
          (if r.rFix then pr_arg str "fix" else mt ()) ++
          (if r.rCofix then pr_arg str "cofix" else mt ())) ++
      (if r.rZeta then pr_arg str "zeta" else mt ()) ++
      (if List.is_empty r.rConst then
          if r.rDelta then pr_arg str "delta"
          else mt ()
        else
          pr_arg str "delta " ++ (if r.rDelta then str "-" else mt ()) ++
            hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]"))

let pr_union pr1 pr2 = function
  | Inl a -> pr1 a
  | Inr b -> pr2 b

let pr_red_expr (pr_constr,pr_lconstr,pr_ref,pr_pattern) keyword = function
  | Red false -> keyword "red"
  | Hnf -> keyword "hnf"
  | Simpl (f,o) -> keyword "simpl" ++ (pr_short_red_flag pr_ref f)
                    ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o
  | Cbv f ->
    if f.rBeta && f.rMatch && f.rFix && f.rCofix &&
          f.rZeta && f.rDelta && List.is_empty f.rConst then
      keyword "compute"
    else
      hov 1 (keyword "cbv" ++ pr_red_flag pr_ref f)
  | Lazy f ->
    hov 1 (keyword "lazy" ++ pr_red_flag pr_ref f)
  | Cbn f ->
    hov 1 (keyword "cbn" ++ pr_red_flag pr_ref f)
  | Unfold l ->
    hov 1 (keyword "unfold" ++ spc() ++
              prlist_with_sep pr_comma (pr_with_occurrences pr_ref keyword) l)
  | Fold l -> hov 1 (keyword "fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
    hov 1 (keyword "pattern" ++
              pr_arg (prlist_with_sep pr_comma (pr_with_occurrences pr_constr keyword)) l)

  | Red true ->
    CErrors.user_err Pp.(str "Shouldn't be accessible from user.")
  | ExtraRedExpr s ->
    str s
  | CbvVm o ->
    keyword "vm_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o
  | CbvNative o ->
    keyword "native_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o

let pr_red_expr_env env sigma (pr_constr,pr_lconstr,pr_ref,pr_pattern) =
  pr_red_expr (pr_constr env sigma, pr_lconstr env sigma, pr_ref, pr_pattern env sigma)

let pr_or_by_notation f = let open Constrexpr in function
  | {CAst.loc; v=AN v} -> f v
  | {CAst.loc; v=ByNotation (s,sc)} -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc

let hov_if_not_empty n p = if Pp.ismt p then p else hov n p

let rec pr_raw_generic env (GenArg (Rawwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_raw_generic env (in_gen (rawwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_raw_generic env (in_gen (rawwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (rawwit wit1) p in
      let q = in_gen (rawwit wit2) q in
      hov_if_not_empty 0 (pr_sequence (pr_raw_generic env) [p; q])
    | ExtraArg s ->
       let open Genprint in
       match generic_raw_print (in_gen (rawwit wit) x) with
       | PrinterBasic pp -> pp ()
       | PrinterNeedsLevel { default_ensure_surrounded; printer } -> printer default_ensure_surrounded


let rec pr_glb_generic env (GenArg (Glbwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_glb_generic env (in_gen (glbwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_glb_generic env (in_gen (glbwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (glbwit wit1) p in
      let q = in_gen (glbwit wit2) q in
      let ans = pr_sequence (pr_glb_generic env) [p; q] in
      hov_if_not_empty 0 ans
    | ExtraArg s ->
       let open Genprint in
       match generic_glb_print (in_gen (glbwit wit) x) with
       | PrinterBasic pp -> pp ()
       | PrinterNeedsLevel { default_ensure_surrounded; printer } -> printer default_ensure_surrounded
