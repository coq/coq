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
open Rawterm
open Term
open Names
open Libnames
open Prim
open Topconstr

let coerce_to_var = function
  | CRef (Ident (_,id)) -> id
  | ast -> Util.user_err_loc
        (constr_loc ast,"Ast.coerce_to_var",
         (Pp.str"This expression should be a simple identifier"))

let coerce_to_name = function
  | CRef (Ident (loc,id)) -> (loc, Name id)
  | ast -> Util.user_err_loc
        (constr_loc ast,"Ast.coerce_to_var",
         (Pp.str"This expression should be a simple identifier"))

open Util

let rec abstract_constr loc c = function
  | [] -> c
  | LocalRawDef ((loc',x),b)::bl ->
      CLetIn (join_loc loc' loc, (loc', x), b, abstract_constr loc c bl)
  | LocalRawAssum (nal,t)::bl ->
      let loc' = join_loc (fst (List.hd nal)) loc in
      CLambdaN(loc', [nal, t], abstract_constr loc c bl)

(* Hack to parse "(n)" as nat without conflicts with the (useless) *)
(* admissible notation "(n)" *)
let test_int_rparen =
  Gram.Entry.of_parser "test_int_rparen"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("INT", _)] ->
            begin match Stream.npeek 2 strm with
              | [_; ("", ")")] -> ()
              | _ -> raise Stream.Failure
            end
        | _ -> raise Stream.Failure)

(* Hack to parse "n" at level 0 without conflicting with "n!" at level 91 *)
(* admissible notation "(n)" *)
let test_int_bang =
  Gram.Entry.of_parser "test_int_bang"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("INT", n)] ->
            begin match Stream.npeek 2 strm with
              | [_; ("", "!")] -> ()
              | _ -> raise Stream.Failure
            end
        | _ -> raise Stream.Failure)

(* Hack to parse "`id:...`" at level 0 without conflicting with
   "`...`" from ZArith *)
let test_ident_colon =
  Gram.Entry.of_parser "test_ident_colon"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("IDENT", _)] ->
            begin match Stream.npeek 2 strm with
              | [_; ("", ":")] -> ()
              | _ -> raise Stream.Failure
            end
        | _ -> raise Stream.Failure)

GEXTEND Gram
  GLOBAL: constr9 lconstr constr sort global constr_pattern Constr.ident
          (*ne_name_comma_list*);
  Constr.ident:
    [ [ id = Prim.ident -> id

      (* This is used in quotations and Syntax *)
      | id = METAIDENT -> id_of_string id ] ]
  ;
  global:
    [ [ r = Prim.reference -> r

      (* This is used in quotations *)
      | id = METAIDENT -> Ident (loc,id_of_string id) ] ]
  ;
  constr_pattern:
    [ [ c = constr -> c ] ]
  ;
  ne_constr_list:
    [ [ cl = LIST1 constr -> cl ] ]
  ;
  sort:
    [ [ "Set"  -> RProp Pos
      | "Prop" -> RProp Null
      | "Type" -> RType None ] ]
  ;
  constr:
    [ "top" RIGHTA
      [ c1 = constr; "->"; c2 = constr -> CArrow (loc, c1, c2) ]
    | "1" RIGHTA
      [ "<"; p = lconstr; ">"; IDENT "Match"; c = constr; "with";
        cl = LIST0 constr; "end" ->
	  COrderedCase (loc, MatchStyle, Some p, c, cl)
      | "<"; p = lconstr; ">"; IDENT "Case"; c = constr; "of";
        cl = LIST0 constr; "end" ->
	  COrderedCase (loc, RegularStyle, Some p, c, cl)
      | IDENT "Case"; c = constr; "of"; cl = LIST0 constr; "end" ->
          COrderedCase (loc, RegularStyle, None, c, cl)
      | IDENT "Match"; c = constr; "with"; cl = LIST1 constr; "end" ->
          COrderedCase (loc, MatchStyle, None, c, cl)
      | IDENT "let"; "("; b = ne_name_comma_list; ")"; "=";
        c = constr; "in"; c1 = constr LEVEL "top"->
          (* TODO: right loc *)
	  COrderedCase
            (loc, LetStyle, None, c, [CLambdaN (loc, [b, CHole loc], c1)])
      | IDENT "let"; na = name; "="; c = opt_casted_constr; 
	"in"; c1 = constr LEVEL "top" ->
          CLetIn (loc, na, c, c1)
      | IDENT "if"; c1 = constr;
        IDENT "then"; c2 = constr;
        IDENT "else"; c3 = constr LEVEL "top" ->
	  COrderedCase (loc, IfStyle, None, c1, [c2; c3])
      | "<"; p = lconstr; ">";
        IDENT "let"; "("; b = ne_name_comma_list; ")"; "="; c = constr; 
        "in"; c1 = constr LEVEL "top" ->
          (* TODO: right loc *)
	  COrderedCase (loc, LetStyle, Some p, c,
            [CLambdaN (loc, [b, CHole loc], c1)])
      | "<"; p = lconstr; ">";
        IDENT "if"; c1 = constr;
        IDENT "then"; c2 = constr; 
        IDENT "else"; c3 = constr LEVEL "top" ->
	  COrderedCase (loc, IfStyle, Some p, c1, [c2; c3]) ]
    | "0" RIGHTA
      [ "?" -> CHole loc
      | "?"; n = Prim.natural -> CMeta (loc, n)
      | bll = binders; c = constr LEVEL "top" -> abstract_constr loc c bll
      (* Hack to parse syntax "(n)" as a natural number *)
      | "("; test_int_rparen; n = bigint; ")" ->
          CDelimiters (loc,"N",CNumeral (loc,n))
      | "("; lc1 = lconstr; ":"; c = constr; (bl,body) = product_tail ->
          let id = coerce_to_name lc1 in
	  CProdN (loc, ([id], c)::bl, body)
(* TODO: Syntaxe (_:t...)t et (_,x...)t *)
      | "("; lc1 = lconstr; ","; lc2 = lconstr; ":"; c = constr;
        (bl,body) = product_tail ->
          let id1 = coerce_to_name lc1 in
          let id2 = coerce_to_name lc2 in
	  CProdN (loc, ([id1; id2], c)::bl, body)
      | "("; lc1 = lconstr; ","; lc2 = lconstr; ",";
        idl = ne_name_comma_list; ":"; c = constr; (bl,body) = product_tail ->
          let id1 = coerce_to_name lc1 in
          let id2 = coerce_to_name lc2 in
	  CProdN (loc, (id1::id2::idl, c)::bl, body)
      | "("; lc1 = lconstr; ")" -> lc1
      | "("; lc1 = lconstr; ")"; "@"; "["; cl = ne_constr_list; "]" ->
	  (match lc1 with
	    | CMeta (loc2,n) -> 
                CApp (loc,CMeta (loc2, -n), List.map (fun c -> c, None) cl)
	    | _ ->
	    Util.error "Second-order pattern-matching expects a head metavariable")
      | IDENT "Fix"; id = identref; "{"; fbinders = fixbinders; "}" ->
	  CFix (loc, id, fbinders)
      | IDENT "CoFix"; id = identref; "{"; fbinders = cofixbinders; "}" ->
	  CCoFix (loc, id, fbinders)
      | s = sort -> CSort (loc, s)
      | v = global -> CRef v
      | n = bigint -> CNumeral (loc,n)
      | "!"; f = global -> CAppExpl (loc,f,[])
      | "'"; test_ident_colon; key = IDENT; ":"; c = constr; "'" -> 
          CDelimiters (loc,key,c) ] ]
  ;
  lconstr:
    [ "10" NONA
      [ "!"; f = global; args = LIST0 constr9 -> CAppExpl (loc, f, args)
(*
      | "!"; f = global; "with"; b = binding_list ->
	  <:ast< (APPLISTWITH $f $b) >>
*)
      | f = constr9; args = LIST1 constr91 -> CApp (loc, f, args)
      | f = constr9 -> f ] ]
  ;
  constr91:
    [ [ test_int_bang; n = INT; "!"; c = constr9 ->
        (c, Some (int_of_string n))
      | c = constr9 -> (c, None) ] ]
  ;
  constr9:
    [ NONA [ c1 = constr -> c1
      | c1 = constr; "::"; c2 = constr -> CCast (loc, c1, c2) ] ]
  ;
  ne_name_comma_list:
    [ [ nal = LIST1 name SEP "," -> nal ] ]
  ;
  name_comma_list_tail:
    [ [ ","; idl = ne_name_comma_list -> idl
      | -> [] ] ]
  ;
  opt_casted_constr:
    [ [ c = constr;  ":"; t = constr -> CCast (loc, c, t)
      | c = constr -> c ] ]
  ;
  vardecls:
    [ [ na = name; nal = name_comma_list_tail; c = type_option ->
          LocalRawAssum (na::nal,c)
      | na = name; "="; c = opt_casted_constr ->
          LocalRawDef (na, c)
      | na = name; ":="; c = opt_casted_constr ->
          LocalRawDef (na, c)

      (* This is used in quotations *)
      | id = METAIDENT; c = type_option -> LocalRawAssum ([loc, Name (id_of_string id)], c)
    ] ]
  ;
  ne_vardecls_list:
    [ [ id = vardecls; ";"; idl = ne_vardecls_list -> id :: idl
      | id = vardecls -> [id] ] ]
  ;
  binders:
    [ [ "["; bl = ne_vardecls_list; "]" -> bl ] ]
  ;
  simple_params:
    [ [ idl = LIST1 name SEP ","; ":"; c = constr -> (idl, c)
      | idl = LIST1 name SEP "," -> (idl, CHole loc)
    ] ]
  ;
  simple_binders:
    [ [ "["; bll = LIST1 simple_params SEP ";"; "]" -> bll ] ]
  ;
  ne_simple_binders_list:
    [ [ bll = LIST1 simple_binders -> List.flatten bll ] ]
  ;
  type_option:
    [ [ ":"; c = constr -> c 
      | -> CHole loc ] ]
  ;
  fixbinder:
    [ [ id = base_ident; "/"; recarg = natural; ":"; type_ = constr;
        ":="; def = constr ->
          (id, recarg-1, type_, def)
      | id = base_ident; bl = ne_simple_binders_list; ":"; type_ = constr;
	":="; def = constr ->
          let ni = List.length (List.flatten (List.map fst bl)) -1 in
          let loc0 = fst (List.hd (fst (List.hd bl))) in
          let loc1 = join_loc loc0 (constr_loc type_) in
          let loc2 = join_loc loc0 (constr_loc def) in
	  (id, ni, CProdN (loc1,bl,type_), CLambdaN (loc2,bl,def)) ] ]
  ;
  fixbinders:
    [ [ fbs = LIST1 fixbinder SEP "with" -> fbs ] ]
  ;
  cofixbinder:
    [ [ id = base_ident; ":"; type_ = constr; ":="; def = constr ->
          (id, type_, def) ] ]
  ;
  cofixbinders:
    [ [ fbs = LIST1 cofixbinder SEP "with" -> fbs ] ]
  ;
  product_tail:
    [ [ ";"; idl = ne_name_comma_list; ":"; c = constr;
        (bl,c2) = product_tail -> ((idl, c)::bl, c2)
      | ";"; idl = ne_name_comma_list; (bl,c2) = product_tail ->
          ((idl, CHole (fst (List.hd idl)))::bl, c2)
      | ")"; c = constr -> ([], c) ] ]
  ;
END;;
