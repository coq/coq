(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pcoq
open Constr
open Topconstr
open Term
open Libnames

open Prim

let pair loc =
  Qualid (loc, Libnames.qualid_of_string "Coq.Init.Datatypes.pair")

if !Options.v7 then
GEXTEND Gram
  GLOBAL: operconstr pattern;

  pattern:
    [ [ r = Prim.reference -> CPatAtom (loc,Some r)
      | IDENT "_" -> CPatAtom (loc,None)
      (* Hack to parse syntax "(n)" as a natural number *)
      | "("; G_constr.test_int_rparen; n = bigint; ")" ->
	  (* Delimiter "N" moved to "nat" in V7 *)
          CPatDelimiters (loc,"nat",CPatNumeral (loc,n))
      | "("; p = compound_pattern; ")" -> p
      | n = bigint -> CPatNumeral (loc,n)
      | "'"; G_constr.test_ident_colon; key = IDENT; ":"; c = pattern; "'" -> 
          CPatDelimiters (loc,key,c)
    ] ]
  ;
  compound_pattern:
    [ [ p = pattern ; lp = LIST1 pattern ->
        (match p with
          | CPatAtom (_, Some r) -> CPatCstr (loc, r, lp)
          | _ -> Util.user_err_loc 
              (loc, "compound_pattern", Pp.str "Constructor expected"))
      | p = pattern; "as"; id = base_ident ->
	  CPatAlias (loc, p, id)
      | p1 = pattern; ","; p2 = pattern ->
	  CPatCstr (loc, pair loc, [p1; p2])
      | p = pattern -> p ] ]
  ;
  equation:
    [ [ lhs = LIST1 pattern; "=>"; rhs = operconstr LEVEL "9" -> (loc,lhs,rhs) ] ]
  ;
  ne_eqn_list:
    [ [ leqn = LIST1 equation SEP "|" -> leqn ] ]
  ;
  operconstr: LEVEL "1"
    [ [ "<"; p = annot; ">"; "Cases"; lc = LIST1 constr; "of";
        OPT "|"; eqs = ne_eqn_list; "end" ->
          let lc = List.map (fun c -> c,(None,None)) lc in
	  CCases (loc, (Some p,None), lc, eqs)
      | "Cases"; lc = LIST1 constr; "of";
	OPT "|"; eqs = ne_eqn_list; "end" ->
          let lc = List.map (fun c -> c,(None,None)) lc in
	  CCases (loc, (None,None), lc, eqs)
      | "<"; p = annot; ">"; "Cases"; lc = LIST1 constr; "of"; "end" ->
          let lc = List.map (fun c -> c,(None,None)) lc in
	  CCases (loc, (Some p,None), lc, [])
      | "Cases"; lc = LIST1 constr; "of"; "end" -> 
          let lc = List.map (fun c -> c,(None,None)) lc in
	  CCases (loc, (None,None), lc, []) ] ]
  ;
END;
