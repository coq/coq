(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pcoq
open Constr
open Topconstr
open Term
open Libnames

open Prim

let pair loc =
  Qualid (loc, Libnames.qualid_of_string "Coq.Init.Datatypes.pair")

GEXTEND Gram
  GLOBAL: constr1 pattern;

  pattern:
    [ [ r = Prim.reference -> CPatAtom (loc,Some r)
      | IDENT "_" -> CPatAtom (loc,None)
      (* Hack to parse syntax "(n)" as a natural number *)
      | "("; G_constr.test_int_rparen; n = INT; ")" ->
	  let n = CPatNumeral (loc,Bignat.POS (Bignat.of_string n)) in
          CPatDelimiters (loc,"nat_scope",n)
      | "("; p = compound_pattern; ")" -> p
      | n = INT -> CPatNumeral (loc,Bignat.POS (Bignat.of_string n))
      | "-"; n = INT -> CPatNumeral (loc,Bignat.NEG (Bignat.of_string n))
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
    [ [ lhs = LIST1 pattern; "=>"; rhs = constr9 -> (loc,lhs,rhs) ] ]
  ;
  ne_eqn_list:
    [ [ leqn = LIST1 equation SEP "|" -> leqn ] ]
  ;

  constr1:
    [ [ "<"; p = lconstr; ">"; "Cases"; lc = LIST1 constr; "of";
        OPT "|"; eqs = ne_eqn_list; "end" ->
	  CCases (loc, Some p, lc, eqs)
      | "Cases"; lc = ne_constr_list; "of";
	OPT "|"; eqs = ne_eqn_list; "end" ->
	  CCases (loc, None, lc, eqs)
      | "<"; p = lconstr; ">"; "Cases"; lc = ne_constr_list; "of"; "end" ->
	  CCases (loc, Some p, lc, [])
      | "Cases"; lc = ne_constr_list; "of"; "end" -> 
	  CCases (loc, None, lc, []) ] ]
  ;
END;
