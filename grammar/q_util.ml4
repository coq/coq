(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file defines standard combinators to build ml expressions *)

open Extend
open Compat

type extend_token =
| ExtTerminal of string
| ExtNonTerminal of Genarg.argument_type * Extend.user_symbol * Names.Id.t

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

let mlexpr_of_token = function
| Tok.KEYWORD s -> <:expr< Tok.KEYWORD $mlexpr_of_string s$ >>
| Tok.METAIDENT s -> <:expr< Tok.METAIDENT $mlexpr_of_string s$ >>
| Tok.PATTERNIDENT s -> <:expr< Tok.PATTERNIDENT $mlexpr_of_string s$ >>
| Tok.IDENT s -> <:expr< Tok.IDENT $mlexpr_of_string s$ >>
| Tok.FIELD s -> <:expr< Tok.FIELD $mlexpr_of_string s$ >>
| Tok.INT s -> <:expr< Tok.INT $mlexpr_of_string s$ >>
| Tok.INDEX s -> <:expr< Tok.INDEX $mlexpr_of_string s$ >>
| Tok.STRING s -> <:expr< Tok.STRING $mlexpr_of_string s$ >>
| Tok.LEFTQMARK -> <:expr< Tok.LEFTQMARK >>
| Tok.BULLET s -> <:expr< Tok.BULLET $mlexpr_of_string s$ >>
| Tok.EOI -> <:expr< Tok.EOI >>

let repr_entry e =
  let entry u =
    let _ = Pcoq.get_entry u e in
    Some (Entry.univ_name u, e)
  in
  try entry Pcoq.uprim with Not_found ->
  try entry Pcoq.uconstr with Not_found ->
  try entry Pcoq.utactic with Not_found -> None

let rec mlexpr_of_prod_entry_key = function
  | Extend.Ulist1 s -> <:expr< Pcoq.Alist1 $mlexpr_of_prod_entry_key s$ >>
  | Extend.Ulist1sep (s,sep) -> <:expr< Pcoq.Alist1sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Extend.Ulist0 s -> <:expr< Pcoq.Alist0 $mlexpr_of_prod_entry_key s$ >>
  | Extend.Ulist0sep (s,sep) -> <:expr< Pcoq.Alist0sep $mlexpr_of_prod_entry_key s$ $str:sep$ >>
  | Extend.Uopt s -> <:expr< Pcoq.Aopt $mlexpr_of_prod_entry_key s$ >>
  | Extend.Umodifiers s -> <:expr< Pcoq.Amodifiers $mlexpr_of_prod_entry_key s$ >>
  | Extend.Uentry e ->
    begin match repr_entry e with
    | None -> <:expr< Pcoq.Aentry (Pcoq.name_of_entry $lid:e$) >>
    | Some (u, s) -> <:expr< Pcoq.Aentry (Entry.unsafe_of_name ($str:u$, $str:s$)) >>
    end
  | Extend.Uentryl (e, l) ->
    (** Keep in sync with Pcoq! *)
    assert (CString.equal e "tactic");
    if l = 5 then <:expr< Pcoq.Aentry (Pcoq.name_of_entry Pcoq.Tactic.binder_tactic) >>
    else <:expr< Pcoq.Aentryl (Pcoq.name_of_entry Pcoq.Tactic.tactic_expr) $mlexpr_of_int l$ >>

let type_entry u e =
  let Pcoq.TypedEntry (t, _) = Pcoq.get_entry u e in
  Genarg.unquote t

let rec type_of_user_symbol = function
| Ulist1 s | Ulist1sep (s, _) | Ulist0 s | Ulist0sep (s, _) | Umodifiers s ->
  Genarg.ListArgType (type_of_user_symbol s)
| Uopt s ->
  Genarg.OptArgType (type_of_user_symbol s)
| Uentry e | Uentryl (e, _) ->
  try type_entry Pcoq.uprim e with Not_found ->
  try type_entry Pcoq.uconstr e with Not_found ->
  try type_entry Pcoq.utactic e with Not_found ->
  Genarg.ExtraArgType e
