(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

let pr_lident { CAst.loc; v=id } =
  let open Names.Id in
  match loc with
  | None     -> print id
  | Some loc -> let (b,_) = Loc.unloc loc in
    pr_located print
      (Some (Loc.make_loc (b,b + String.length (to_string id))), id)

let pr_lname = let open Names in function
  | {CAst.loc; v=Name id} -> pr_lident CAst.(make ?loc id)
  | x -> pr_ast Name.print x

let pr_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar id -> pr_lident id

let pr_or_by_notation f = let open Constrexpr in CAst.with_val (function
    | AN v -> f v
    | ByNotation (s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc)

let hov_if_not_empty n p = if Pp.ismt p then p else hov n p

let rec pr_raw_generic env sigma (GenArg (Rawwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_raw_generic env sigma (in_gen (rawwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_raw_generic env sigma (in_gen (rawwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (rawwit wit1) p in
      let q = in_gen (rawwit wit2) q in
      hov_if_not_empty 0 (pr_sequence (pr_raw_generic env sigma) [p; q])
    | ExtraArg s ->
       let open Genprint in
       match generic_raw_print (in_gen (rawwit wit) x) with
       | PrinterBasic pp -> pp env sigma
       | PrinterNeedsLevel { default_ensure_surrounded; printer } ->
         printer env sigma default_ensure_surrounded


let rec pr_glb_generic env sigma (GenArg (Glbwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_glb_generic env sigma (in_gen (glbwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_glb_generic env sigma (in_gen (glbwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (glbwit wit1) p in
      let q = in_gen (glbwit wit2) q in
      let ans = pr_sequence (pr_glb_generic env sigma) [p; q] in
      hov_if_not_empty 0 ans
    | ExtraArg s ->
       let open Genprint in
       match generic_glb_print (in_gen (glbwit wit) x) with
       | PrinterBasic pp -> pp env sigma
       | PrinterNeedsLevel { default_ensure_surrounded; printer } ->
         printer env sigma default_ensure_surrounded
