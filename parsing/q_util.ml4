(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file defines standard combinators to build ml expressions *)

open Extrawit
open Compat
open Util

let mlexpr_of_list f l =
  List.fold_right
    (fun e1 e2 ->
      let e1 = f e1 in
       let loc = join_loc (MLast.loc_of_expr e1) (MLast.loc_of_expr e2) in
       <:expr< [$e1$ :: $e2$] >>)
    l (let loc = dummy_loc in <:expr< [] >>)

let mlexpr_of_pair m1 m2 (a1,a2) =
  let e1 = m1 a1 and e2 = m2 a2 in
  let loc = join_loc (MLast.loc_of_expr e1) (MLast.loc_of_expr e2) in
  <:expr< ($e1$, $e2$) >>

let mlexpr_of_triple m1 m2 m3 (a1,a2,a3)=
  let e1 = m1 a1 and e2 = m2 a2 and e3 = m3 a3 in
  let loc = join_loc (MLast.loc_of_expr e1) (MLast.loc_of_expr e3) in
  <:expr< ($e1$, $e2$, $e3$) >>

let mlexpr_of_quadruple m1 m2 m3 m4 (a1,a2,a3,a4)=
  let e1 = m1 a1 and e2 = m2 a2 and e3 = m3 a3 and e4 = m4 a4 in
  let loc = join_loc (MLast.loc_of_expr e1) (MLast.loc_of_expr e4) in
  <:expr< ($e1$, $e2$, $e3$, $e4$) >>

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

open Vernacexpr
open Pcoq
open Genarg

let rec mlexpr_of_prod_entry_key = function
  | Alist1 s -> <:expr< Alist1 $mlexpr_of_prod_entry_key s$ >>
  | Alist1sep (s,sep) -> <:expr< Alist1sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Alist0 s -> <:expr< Alist0 $mlexpr_of_prod_entry_key s$ >>
  | Alist0sep (s,sep) -> <:expr< Alist0sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Aopt s -> <:expr< Aopt $mlexpr_of_prod_entry_key s$ >>
  | Amodifiers s -> <:expr< Amodifiers $mlexpr_of_prod_entry_key s$ >>
  | Aself -> <:expr< Aself >>
  | Anext -> <:expr< Anext >>
  | Atactic n -> <:expr< Atactic $mlexpr_of_int n$ >>
  | Agram s -> Util.anomaly "Agram not supported"
  | Aentry ("",s) -> <:expr< Agram (Gram.Entry.obj $lid:s$) >>
  | Aentry (u,s) -> <:expr< Aentry $str:u$ $str:s$ >>
