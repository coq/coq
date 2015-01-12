(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file defines standard combinators to build ml expressions *)

open Compat

let mlexpr_of_list f l =
  List.fold_right
    (fun e1 e2 ->
      let e1 = f e1 in
       let loc = CompatLoc.merge (MLast.loc_of_expr e1) (MLast.loc_of_expr e2) in
       <:expr< [$e1$ :: $e2$] >>)
    l (let loc = CompatLoc.ghost in <:expr< [] >>)

let mlexpr_of_pair m1 m2 (a1,a2) =
  let e1 = m1 a1 and e2 = m2 a2 in
  let loc = CompatLoc.merge (MLast.loc_of_expr e1) (MLast.loc_of_expr e2) in
  <:expr< ($e1$, $e2$) >>

let mlexpr_of_triple m1 m2 m3 (a1,a2,a3)=
  let e1 = m1 a1 and e2 = m2 a2 and e3 = m3 a3 in
  let loc = CompatLoc.merge (MLast.loc_of_expr e1) (MLast.loc_of_expr e3) in
  <:expr< ($e1$, $e2$, $e3$) >>

let mlexpr_of_quadruple m1 m2 m3 m4 (a1,a2,a3,a4)=
  let e1 = m1 a1 and e2 = m2 a2 and e3 = m3 a3 and e4 = m4 a4 in
  let loc = CompatLoc.merge (MLast.loc_of_expr e1) (MLast.loc_of_expr e4) in
  <:expr< ($e1$, $e2$, $e3$, $e4$) >>

(* We don't give location for tactic quotation! *)
let loc = CompatLoc.ghost


let mlexpr_of_bool = function
  | true -> <:expr< True >>
  | false -> <:expr< False >>

let mlexpr_of_int n = <:expr< $int:string_of_int n$ >>

let mlexpr_of_string s = <:expr< $str:s$ >>

let mlexpr_of_option f = function
  | None -> <:expr< None >>
  | Some e -> <:expr< Some $f e$ >>

let rec mlexpr_of_prod_entry_key = function
  | Pcoq.Alist1 s -> <:expr< Pcoq.Alist1 $mlexpr_of_prod_entry_key s$ >>
  | Pcoq.Alist1sep (s,sep) -> <:expr< Pcoq.Alist1sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Pcoq.Alist0 s -> <:expr< Pcoq.Alist0 $mlexpr_of_prod_entry_key s$ >>
  | Pcoq.Alist0sep (s,sep) -> <:expr< Pcoq.Alist0sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Pcoq.Aopt s -> <:expr< Pcoq.Aopt $mlexpr_of_prod_entry_key s$ >>
  | Pcoq.Amodifiers s -> <:expr< Pcoq.Amodifiers $mlexpr_of_prod_entry_key s$ >>
  | Pcoq.Aself -> <:expr< Pcoq.Aself >>
  | Pcoq.Anext -> <:expr< Pcoq.Anext >>
  | Pcoq.Atactic n -> <:expr< Pcoq.Atactic $mlexpr_of_int n$ >>
  | Pcoq.Agram s -> Errors.anomaly (Pp.str "Agram not supported")
  | Pcoq.Aentry ("",s) -> <:expr< Pcoq.Agram (Pcoq.Gram.Entry.name $lid:s$) >>
  | Pcoq.Aentry (u,s) -> <:expr< Pcoq.Aentry $str:u$ $str:s$ >>
