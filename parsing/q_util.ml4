(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* This file defines standard combinators to build ml expressions *)

open Util

let not_impl name x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else 
      "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("<Q_util." ^ name ^ ", not impl: " ^ desc)

let rec patt_of_expr e =
  let loc = MLast.loc_of_expr e in
  match e with
    | <:expr< $e1$.$e2$ >> -> <:patt< $patt_of_expr e1$.$patt_of_expr e2$ >>
    | <:expr< $e1$ $e2$ >> -> <:patt< $patt_of_expr e1$ $patt_of_expr e2$ >>
    | <:expr< loc >> -> <:patt< _ >>
    | <:expr< $lid:s$ >> -> <:patt< $lid:s$ >>
    | <:expr< $uid:s$ >> -> <:patt< $uid:s$ >>
    | <:expr< $str:s$ >> -> <:patt< $str:s$ >>
    | <:expr< $anti:e$ >> -> <:patt< $anti:patt_of_expr e$ >>
    | _ -> not_impl "patt_of_expr" e

let mlexpr_of_list f l =
  List.fold_right
    (fun e1 e2 ->
      let e1 = f e1 in
       let loc = (fst (MLast.loc_of_expr e1), snd (MLast.loc_of_expr e2)) in
       <:expr< [$e1$ :: $e2$] >>)
    l (let loc = dummy_loc in <:expr< [] >>)

let mlexpr_of_pair m1 m2 (a1,a2) =
  let e1 = m1 a1 and e2 = m2 a2 in
  let loc = (fst (MLast.loc_of_expr e1), snd (MLast.loc_of_expr e2)) in
  <:expr< ($e1$, $e2$) >>

let mlexpr_of_triple m1 m2 m3 (a1,a2,a3)=
  let e1 = m1 a1 and e2 = m2 a2 and e3 = m3 a3 in
  let loc = (fst (MLast.loc_of_expr e1), snd (MLast.loc_of_expr e3)) in
  <:expr< ($e1$, $e2$, $e3$) >>

(* We don't give location for tactic quotation! *)
let loc = dummy_loc


let mlexpr_of_bool = function
  | true -> <:expr< True >>
  | false -> <:expr< False >>

let mlexpr_of_int n = <:expr< $int:string_of_int n$ >>

let mlexpr_of_string s = <:expr< $str:s$ >>

let mlexpr_of_option f = function
  | None -> <:expr< None >>
  | Some e -> <:expr< Some $f e$ >>
