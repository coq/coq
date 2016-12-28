(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Genarg
open Nameops
open Misctypes
open Locus
open Genredexpr

let pr_located pr (loc, x) =
  if !Flags.beautify && loc <> Loc.ghost then
    let (b, e) = Loc.unloc loc in
    (* Side-effect: order matters *)
    let before = Pp.comment (CLexer.extract_comments b) in
    let x = pr x in
    let after = Pp.comment (CLexer.extract_comments e) in
    before ++ x ++ after
  else pr x

let pr_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (_,s) -> pr_id s

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
  with complexRedFlags ->
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
    CErrors.error "Shouldn't be accessible from user."
  | ExtraRedExpr s ->
    str s
  | CbvVm o ->
    keyword "vm_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o
  | CbvNative o ->
    keyword "native_compute" ++ pr_opt (pr_with_occurrences (pr_union pr_ref pr_pattern) keyword) o

let pr_or_by_notation f = function
  | AN v -> f v
  | ByNotation (_,s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc

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
      Genprint.generic_raw_print (in_gen (rawwit wit) x)


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
      Genprint.generic_glb_print (in_gen (glbwit wit) x)
