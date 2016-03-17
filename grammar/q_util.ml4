(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file defines standard combinators to build ml expressions *)

open Extend
open Compat

type extend_token =
| ExtTerminal of string
| ExtNonTerminal of Genarg.argument_type * Extend.user_symbol * string

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

let mlexpr_of_ident id =
  <:expr< Names.Id.of_string $str:id$ >>

let rec mlexpr_of_prod_entry_key f = function
  | Extend.Ulist1 s -> <:expr< Pcoq.Alist1 $mlexpr_of_prod_entry_key f s$ >>
  | Extend.Ulist1sep (s,sep) -> <:expr< Pcoq.Alist1sep $mlexpr_of_prod_entry_key f s$ $str:sep$ >>
  | Extend.Ulist0 s -> <:expr< Pcoq.Alist0 $mlexpr_of_prod_entry_key f s$ >>
  | Extend.Ulist0sep (s,sep) -> <:expr< Pcoq.Alist0sep $mlexpr_of_prod_entry_key f s$ $str:sep$ >>
  | Extend.Uopt s -> <:expr< Pcoq.Aopt $mlexpr_of_prod_entry_key f s$ >>
  | Extend.Umodifiers s -> <:expr< Pcoq.Amodifiers $mlexpr_of_prod_entry_key f s$ >>
  | Extend.Uentry e -> <:expr< Pcoq.Aentry $f e$ >>
  | Extend.Uentryl (e, l) ->
    (** Keep in sync with Pcoq! *)
    assert (CString.equal e "tactic");
    if l = 5 then <:expr< Pcoq.Aentry (Pcoq.name_of_entry Pcoq.Tactic.binder_tactic) >>
    else <:expr< Pcoq.Aentryl (Pcoq.name_of_entry Pcoq.Tactic.tactic_expr) $mlexpr_of_int l$ >>

let rec type_of_user_symbol = function
| Ulist1 s | Ulist1sep (s, _) | Ulist0 s | Ulist0sep (s, _) | Umodifiers s ->
  Genarg.ListArgType (type_of_user_symbol s)
| Uopt s ->
  Genarg.OptArgType (type_of_user_symbol s)
| Uentry e | Uentryl (e, _) -> Genarg.ExtraArgType e
