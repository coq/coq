(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "q_MLast.cmo" i*)

(* $Id$ *)

(* This file defines standard combinators to build ml expressions *)

open Util
open Extrawit
open Pcoq

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
  | Extend.Alist1 s -> <:expr< Extend.Alist1 $mlexpr_of_prod_entry_key s$ >>
  | Extend.Alist1sep (s,sep) -> <:expr< Extend.Alist1sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Extend.Alist0 s -> <:expr< Extend.Alist0 $mlexpr_of_prod_entry_key s$ >>
  | Extend.Alist0sep (s,sep) -> <:expr< Extend.Alist0sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Extend.Aopt s -> <:expr< Extend.Aopt $mlexpr_of_prod_entry_key s$ >>
  | Extend.Amodifiers s -> <:expr< Extend.Amodifiers $mlexpr_of_prod_entry_key s$ >>
  | Extend.Aself -> <:expr< Extend.Aself >>
  | Extend.Anext -> <:expr< Extend.Anext >>
  | Extend.Atactic n -> <:expr< Extend.Atactic $mlexpr_of_int n$ >>
  | Extend.Agram s -> anomaly "Agram not supported"
  | Extend.Aentry ("",s) -> <:expr< Extend.Agram (Gram.Entry.obj $lid:s$) >>
  | Extend.Aentry (u,s) -> <:expr< Extend.Aentry $str:u$ $str:s$ >>
