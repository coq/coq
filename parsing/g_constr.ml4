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
open Rawterm
open Term
open Names
open Libnames
open Prim
open Topconstr

(* Initialize the lexer *)
let constr_kw =
  [ "Cases"; "of"; "with"; "end"; "as"; "in"; "Prop"; "Set"; "Type";
    ":"; "("; ")"; "["; "]"; "{"; "}"; ","; ";"; "->"; "="; ":="; "!";
    "::"; "<:"; ":<"; "=>"; "<"; ">"; "|"; "?"; "/";
    "<->"; "\\/"; "/\\"; "`"; "``"; "&"; "*"; "+"; "@"; "^"; "#"; "-";
    "~"; "'"; "<<"; ">>"; "<>"
  ]
let _ =
  if !Options.v7 then
  List.iter (fun s -> Lexer.add_token ("",s)) constr_kw
(* "let" is not a keyword because #Core#let.cci would not parse.
   Is it still accurate ? *)


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

let set_loc loc = function
  | CRef(Ident(_,i)) -> CRef(Ident(loc,i))
  | CRef(Qualid(_,q)) -> CRef(Qualid(loc,q))
  | CFix(_,x,a) -> CFix(loc,x,a)
  | CCoFix(_,x,a) -> CCoFix(loc,x,a)
  | CArrow(_,a,b) -> CArrow(loc,a,b)
  | CProdN(_,bl,a) -> CProdN(loc,bl,a)
  | CLambdaN(_,bl,a) -> CLambdaN(loc,bl,a)
  | CLetIn(_,x,a,b) -> CLetIn(loc,x,a,b)
  | CAppExpl(_,f,a) -> CAppExpl(loc,f,a)
  | CApp(_,f,a) -> CApp(loc,f,a)
  | CCases(_,p,a,br) -> CCases(loc,p,a,br)
  | COrderedCase(_,s,p,a,br) -> COrderedCase(loc,s,p,a,br)
  | CLetTuple(_,ids,p,a,b) -> CLetTuple(loc,ids,p,a,b)
  | CIf(_,e,p,a,b) -> CIf(loc,e,p,a,b)
  | CHole _ -> CHole loc
  | CPatVar(_,v) -> CPatVar(loc,v)
  | CEvar(_,ev) -> CEvar(loc,ev)
  | CSort(_,s) -> CSort(loc,s)
  | CCast(_,a,b) -> CCast(loc,a,b)
  | CNotation(_,n,l) -> CNotation(loc,n,l)
  | CNumeral(_,i) -> CNumeral(loc,i)
  | CDelimiters(_,s,e) -> CDelimiters(loc,s,e)
  | CDynamic(_,d) -> CDynamic(loc,d)

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


if !Options.v7 then
GEXTEND Gram
  GLOBAL: operconstr lconstr constr sort global constr_pattern Constr.ident annot
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
    [ [ c = operconstr LEVEL "8" -> c ] ]
  ;
  lconstr:
    [ [ c = operconstr LEVEL "10" -> c ] ]
  ;
  operconstr:
    [ "10" RIGHTA
      [ "!"; f = global; args = LIST0 (operconstr LEVEL "9") ->
          CAppExpl (loc, (None,f), args)
(*
      | "!"; f = global; "with"; b = binding_list ->
	  <:ast< (APPLISTWITH $f $b) >>
*)
      | f = operconstr; args = LIST1 constr91 -> CApp (loc, (None,f), args) ]
    | "9" RIGHTA
      [ c1 = operconstr; "::"; c2 = operconstr LEVEL "9" -> CCast (loc, c1, c2) ]
    | "8" RIGHTA
      [ c1 = operconstr; "->"; c2 = operconstr LEVEL "8"-> CArrow (loc, c1, c2) ]
    | "1" RIGHTA
      [ "<"; p = annot; ">"; IDENT "Match"; c = constr; "with";
        cl = LIST0 constr; "end" ->
	  COrderedCase (loc, MatchStyle, Some p, c, cl)
      | "<"; p = annot; ">"; IDENT "Case"; c = constr; "of";
        cl = LIST0 constr; "end" ->
	  COrderedCase (loc, RegularStyle, Some p, c, cl)
      | IDENT "Case"; c = constr; "of"; cl = LIST0 constr; "end" ->
          COrderedCase (loc, RegularStyle, None, c, cl)
      | IDENT "Match"; c = constr; "with"; cl = LIST1 constr; "end" ->
          COrderedCase (loc, MatchStyle, None, c, cl)
      | IDENT "let"; "("; b = ne_name_comma_list; ")"; "=";
        c = constr; "in"; c1 = constr ->
          (* TODO: right loc *)
	  COrderedCase
            (loc, LetStyle, None, c, [CLambdaN (loc, [b, CHole loc], c1)])
      | IDENT "let"; na = name; "="; c = opt_casted_constr; 
	"in"; c1 = constr ->
          CLetIn (loc, na, c, c1)
      | IDENT "if"; c1 = constr;
        IDENT "then"; c2 = constr;
        IDENT "else"; c3 = constr ->
	  COrderedCase (loc, IfStyle, None, c1, [c2; c3])
      | "<"; p = annot; ">";
        IDENT "let"; "("; b = ne_name_comma_list; ")"; "="; c = constr; 
        "in"; c1 = constr ->
          (* TODO: right loc *)
	  COrderedCase (loc, LetStyle, Some p, c,
            [CLambdaN (loc, [b, CHole loc], c1)])
      | "<"; p = annot; ">";
        IDENT "if"; c1 = constr;
        IDENT "then"; c2 = constr; 
        IDENT "else"; c3 = constr ->
	  COrderedCase (loc, IfStyle, Some p, c1, [c2; c3])
      | ".."; c = operconstr LEVEL "0"; ".." ->
          CAppExpl (loc,(None,Ident (loc,Topconstr.ldots_var)),[c]) ]
    | "0" RIGHTA
      [ "?" -> CHole loc
      | "?"; n = Prim.natural -> CPatVar (loc, (false,Pattern.patvar_of_int n))
      | bll = binders; c = constr -> abstract_constr loc c bll
      (* Hack to parse syntax "(n)" as a natural number *)
      | "("; test_int_rparen; n = bigint; ")" ->
	  (* Delimiter "N" moved to "nat" in V7 *)
          CDelimiters (loc,"nat",CNumeral (loc,n))
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
      | "("; lc1 = lconstr; ")" ->
          if Options.do_translate() then set_loc loc lc1 else lc1
      | "("; lc1 = lconstr; ")"; "@"; "["; cl = ne_constr_list; "]" ->
	  (match lc1 with
	    | CPatVar (loc2,(false,n)) -> 
                CApp (loc,(None,CPatVar (loc2, (true,n))), List.map (fun c -> c, None) cl)
	    | _ ->
	    Util.error "Second-order pattern-matching expects a head metavariable")
      | IDENT "Fix"; id = identref; "{"; fbinders = fixbinders; "}" ->
	  CFix (loc, id, fbinders)
      | IDENT "CoFix"; id = identref; "{"; fbinders = cofixbinders; "}" ->
	  CCoFix (loc, id, fbinders)
      | IDENT "Prefix" ; "(" ;  s = STRING ; cl = LIST0 constr ; ")" ->
	  CNotation(loc, s, cl)
      | s = sort -> CSort (loc, s)
      | v = global -> CRef v
      | n = bigint -> CNumeral (loc,n)
      | "!"; f = global -> CAppExpl (loc,(None,f),[])
      | "'"; test_ident_colon; key = IDENT; ":"; c = constr; "'" -> 
	  (* Delimiter "N" implicitly moved to "nat" in V7 *)
	  let key = if key = "N" then "nat" else key in
	  let key = if key = "P" then "positive" else key in
	  let key = if key = "T" then "type" else key in
	  CDelimiters (loc,key,c) ] ]
  ;
  constr91:
    [ [ test_int_bang; n = INT; "!"; c = operconstr LEVEL "9" ->
        (c, Some (loc,ExplByPos (int_of_string n)))
      | c = operconstr LEVEL "9" -> (c, None) ] ]
  ;
  (* annot and product_annot_tail are hacks to forbid concrete syntax *)
  (* ">" (e.g. for gt, Zgt, ...) in annotations *)
  annot:
    [ RIGHTA
      [ bll = binders; c = annot -> abstract_constr loc c bll 
      | "("; lc1 = lconstr; ":"; c = constr; (bl,body) = product_annot_tail ->
          let id = coerce_to_name lc1 in
	  CProdN (loc, ([id], c)::bl, body)
      | "("; lc1 = lconstr; ","; lc2 = lconstr; ":"; c = constr;
        (bl,body) = product_annot_tail ->
          let id1 = coerce_to_name lc1 in
          let id2 = coerce_to_name lc2 in
	  CProdN (loc, ([id1; id2], c)::bl, body)
      | "("; lc1 = lconstr; ","; lc2 = lconstr; ",";
        idl = ne_name_comma_list; ":"; c = constr;
	(bl,body) = product_annot_tail ->
          let id1 = coerce_to_name lc1 in
          let id2 = coerce_to_name lc2 in
	  CProdN (loc, (id1::id2::idl, c)::bl, body)
      | "("; lc1 = lconstr; ")" -> lc1
      | c1 = annot; "->"; c2 = annot -> CArrow (loc, c1, c2) ]
    | RIGHTA 
      [ c1 = annot; "\\/"; c2 = annot -> CNotation (loc, "_ \\/ _", [c1;c2]) ]
    | RIGHTA
      [ c1 = annot; "/\\"; c2 = annot -> CNotation (loc, "_ /\\ _", [c1;c2]) ]
    | RIGHTA
      [ "~"; c = SELF -> CNotation (loc, "~ _", [c]) ]
    | RIGHTA
      [ c1 = SELF; "=="; c2 = NEXT -> CNotation (loc, "_ == _", [c1;c2]) ]
    | RIGHTA
      [ c1 = SELF; "="; c2 = NEXT -> CNotation (loc, "_ = _", [c1;c2]) ]
    | [ c = operconstr LEVEL "4L" -> c ] ]
  ;
  product_annot_tail:
    [ [ ";"; idl = ne_name_comma_list; ":"; c = constr;
        (bl,c2) = product_annot_tail -> ((idl, c)::bl, c2)
      | ";"; idl = ne_name_comma_list; (bl,c2) = product_annot_tail ->
          ((idl, CHole (fst (List.hd idl)))::bl, c2)
      | ")"; c = annot -> ([], c) ] ]
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
          (id, recarg-1, [], type_, def)
      | id = base_ident; bl = ne_simple_binders_list; ":"; type_ = constr;
	":="; def = constr ->
          let ni = List.length (List.flatten (List.map fst bl)) -1 in
          let bl = List.map (fun(nal,ty)->LocalRawAssum(nal,ty)) bl in
	  (id, ni, bl, type_, def) ] ]
  ;
  fixbinders:
    [ [ fbs = LIST1 fixbinder SEP "with" -> fbs ] ]
  ;
  cofixbinder:
    [ [ id = base_ident; ":"; type_ = constr; ":="; def = constr ->
          (id, [],type_, def) ] ]
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
