(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg

type 'a printer_without_level = 'a -> std_ppcmds
type 'a printer_with_level = Ppextend.tolerability -> 'a -> std_ppcmds
type 'a printer = Ppextend.tolerability option -> 'a -> std_ppcmds

type ('raw, 'glb, 'top) genprinter = {
  raw : 'raw printer;
  glb : 'glb printer;
  top : 'top printer;
}

module PrintObj =
struct
  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) genprinter
  let name = "printer"
  let default wit = match wit with
  | ExtraArg tag ->
    let name = ArgT.repr tag in
    let printer = {
      raw = (fun _ _ -> str "<genarg:" ++ str name ++ str ">");
      glb = (fun _ _ -> str "<genarg:" ++ str name ++ str ">");
      top = (fun _ _ -> str "<genarg:" ++ str name ++ str ">");
    } in
    Some printer
  | _ -> assert false
end

module Print = Register (PrintObj)

let register_print0 wit raw glb top =
  let raw = function None -> raw | _ -> raw in
  let glb = function None -> glb | _ -> glb in
  let top = function None -> top | _ -> top in
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let register_print_with_level0 wit raw glb top =
  let raw = function Some l -> raw l | _ -> CErrors.anomaly (Pp.str "Level expected") in
  let glb = function Some l -> glb l | _ -> CErrors.anomaly (Pp.str "Level expected") in
  let top = function Some l -> top l | _ -> CErrors.anomaly (Pp.str "Level expected") in
  let printer = { raw; glb; top; } in
  Print.register0 wit printer

let raw_print wit v = (Print.obj wit).raw v
let glb_print wit v = (Print.obj wit).glb v
let top_print wit v = (Print.obj wit).top v

let generic_raw_print x (GenArg (Rawwit w, v)) = raw_print w x v
let generic_glb_print x (GenArg (Glbwit w, v)) = glb_print w x v
let generic_top_print x (GenArg (Topwit w, v)) = top_print w x v

let hov_if_not_empty n p = if Pp.ismt p then p else hov n p

let rec pr_raw_generic env lev (GenArg (Rawwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_raw_generic env lev (in_gen (rawwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_raw_generic env lev (in_gen (rawwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (rawwit wit1) p in
      let q = in_gen (rawwit wit2) q in
      hov_if_not_empty 0 (pr_sequence (pr_raw_generic env lev) [p; q])
    | ExtraArg s ->
      generic_raw_print lev (in_gen (rawwit wit) x)


let rec pr_glb_generic env lev (GenArg (Glbwit wit, x)) =
  match wit with
    | ListArg wit ->
      let map x = pr_glb_generic env lev (in_gen (glbwit wit) x) in
      let ans = pr_sequence map x in
      hov_if_not_empty 0 ans
    | OptArg wit ->
      let ans = match x with
        | None -> mt ()
        | Some x -> pr_glb_generic env lev (in_gen (glbwit wit) x)
      in
      hov_if_not_empty 0 ans
    | PairArg (wit1, wit2) ->
      let p, q = x in
      let p = in_gen (glbwit wit1) p in
      let q = in_gen (glbwit wit2) q in
      let ans = pr_sequence (pr_glb_generic env lev) [p; q] in
      hov_if_not_empty 0 ans
    | ExtraArg s ->
      generic_glb_print lev (in_gen (glbwit wit) x)
