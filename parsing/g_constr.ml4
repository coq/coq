(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pcoq
open Constr

GEXTEND Gram
  GLOBAL: ident constr0 constr1 constr2 constr3 lassoc_constr4 constr5
          constr6 constr7 constr8 constr9 constr10 lconstr constr
          ne_ident_comma_list ne_constr_list sort ne_binders_list qualid
          global;
  ident:
    [ [ id = IDENT -> <:ast< ($VAR $id) >> 

      (* This is used in quotations *)
      | id = METAIDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  global:
    [ [ l = qualid -> <:ast< (QUALID ($LIST l)) >>

      (* This is used in quotations *)
      | id = METAIDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  qualid:
    [ [ id = IDENT; l = fields -> <:ast< ($VAR $id) >> :: l ] ]
  ;
  fields:
    [ [ id = FIELD; l = fields -> <:ast< ($VAR $id) >> :: l
      | -> []
      ] ]
  ;
  raw_constr:
    [ [ c = Prim.ast -> c ] ]
  ;
  constr:
    [ [ c = constr8 -> c 
      | IDENT "Context"; id = ident; IDENT "With"; c = constr8 ->
        <:ast< (CONTEXT $id $c) >>
      | IDENT "Eval"; rtc = Tactic.red_tactic; "in"; c = constr8 ->
        <:ast< (EVAL $c (REDEXP $rtc)) >> ] ]
  ;
  lconstr:
    [ [ c = constr10 -> c ] ]
  ;
  ne_constr_list:
    [ [ c1 = constr; cl = ne_constr_list -> c1::cl
      | c1 = constr -> [c1] ] ]
  ;
  sort:
    [ [ "Set"  -> <:ast< (SET) >>
      | "Prop" -> <:ast< (PROP) >>
      | "Type" -> <:ast< (TYPE) >> ] ]
  ;
  constr0:
    [ [ "?" -> <:ast< (ISEVAR) >>
      | "?"; n = Prim.number -> <:ast< (META $n) >>
      | bl = binders; c = constr -> <:ast< ($ABSTRACT "LAMBDALIST" $bl $c) >>
      | "("; lc1 = lconstr; ":"; c = constr; body = product_tail ->
          let id = Ast.coerce_to_var "lc1" lc1 in
            <:ast< (PROD $c [$id]$body) >>
      | "("; lc1 = lconstr; ","; lc2 = lconstr; ":"; c = constr; 
        body = product_tail ->
          let id1 = Ast.coerce_to_var "lc1" lc1 in
          let id2 = Ast.coerce_to_var "lc2" lc2 in
            <:ast< (PRODLIST $c [$id1][$id2]$body) >>
      | "("; lc1 = lconstr; ","; lc2 = lconstr; ",";
        idl = ne_ident_comma_list; ":"; c = constr; body = product_tail ->
          let id1 = Ast.coerce_to_var "lc1" lc1 in
          let id2 = Ast.coerce_to_var "lc2" lc2 in
            <:ast< (PRODLIST $c [$id1][$id2]($SLAM $idl $body)) >>
      | "("; lc1 = lconstr; ")" -> lc1
      | "("; lc1 = lconstr; ")"; "@"; "["; cl = ne_constr_list; "]" ->
          <:ast< (SOAPP $lc1 ($LIST $cl)) >>
      | IDENT "Fix"; id = ident; "{"; fbinders = fixbinders; "}" ->
          <:ast< (FIX $id ($LIST $fbinders)) >>
      | IDENT "CoFix"; id = ident; "{"; fbinders = cofixbinders; "}" ->
          <:ast< (COFIX $id ($LIST $fbinders)) >>
      | s = sort -> s
      | v = global -> v
  ] ]
  ;
  constr1:
    [ [ "<"; ":"; IDENT "ast"; ":"; "<"; c = raw_constr; ">>" -> c
      | "<"; l1 = lconstr; ">"; IDENT "Match"; c = constr; "with";
        cl = ne_constr_list; "end" ->
          <:ast< (CASE "REC" $l1 $c ($LIST $cl)) >>
      | "<"; l1 = lconstr; ">"; IDENT "Match"; c = constr; "with"; "end"
        ->
          <:ast< (CASE "REC" $l1 $c) >>
      | "<"; l1 = lconstr; ">"; IDENT "Case"; c = constr; "of";
        cl = ne_constr_list; "end" ->
          <:ast< (CASE "NOREC" $l1 $c ($LIST $cl)) >>
      | "<"; l1 = lconstr; ">"; IDENT "Case"; c = constr; "of"; "end" ->
          <:ast< (CASE "NOREC" $l1 $c) >>
      | IDENT "Case"; c = constr; "of"; cl = ne_constr_list; "end" ->
          <:ast< (CASE "NOREC" "SYNTH" $c ($LIST $cl)) >>
      | IDENT "Case"; c = constr; "of"; "end" ->
          <:ast< (CASE "NOREC" "SYNTH" $c) >>
      | IDENT "Match"; c = constr; "with"; cl = ne_constr_list; "end" ->
          <:ast< (CASE "REC" "SYNTH" $c ($LIST $cl)) >>
      | IDENT "let"; "("; b = ne_ident_comma_list; ")"; "=";
        c = constr; "in"; c1 = constr ->
          <:ast< (CASE "NOREC" "SYNTH" $c (LAMBDALIST (ISEVAR)
                   ($SLAM $b $c1))) >>
      | IDENT "let"; id1 = IDENT ; "="; c = constr; "in"; c1 = constr -> 
	  <:ast< (LETIN $c [$id1]$c1) >>
      | IDENT "if"; c1 = constr; IDENT "then"; c2 = constr;
        IDENT "else"; c3 = constr ->
        <:ast< ( CASE "NOREC" "SYNTH" $c1 $c2 $c3) >>
(* EN ATTENTE DE REMPLACER CE QUI EST DANS Program.v ... *)
      | "<"; l1 = lconstr; ">";
        IDENT "let"; "("; b = ne_ident_comma_list; ")"; "=";
        c = constr; "in"; c1 = constr ->
         <:ast< (CASE "NOREC" $l1 $c (LAMBDALIST (ISEVAR) ($SLAM $b $c1))) >>
      | "<"; l1 = lconstr; ">";
        IDENT "if"; c1 = constr; IDENT "then";
        c2 = constr; IDENT "else"; c3 = constr ->
          <:ast< (CASE "NOREC" $l1 $c1 $c2 $c3) >>
      | c = constr0 -> c ] ]
  ;
  constr2: (* ~ will be here *)
    [ [ c = constr1 -> c ] ]
  ;
  constr3:
    [ [ c1 = constr2 -> c1 ] ]
  ;
  lassoc_constr4:
    [ [ c1 = constr3 -> c1 ] ]
  ;
  constr5:
    [ [ c1 = lassoc_constr4 -> c1 ] ]
  ;
  constr6:  (* /\ will be here *)
    [ [ c1 = constr5 -> c1 ] ]
  ;
  constr7:  (* \/ will be here *)
    [ RIGHTA [ c1 = constr6 -> c1 ] ]
  ;
  constr8:  (* <-> will be here *)
    [ [ c1 = constr7 -> c1
      | c1 = constr7; "->"; c2 = constr8 -> <:ast< (PROD $c1 [<>]$c2) >> ] ]
  ;
  constr9:
    [ [ c1 = constr8 -> c1
      | c1 = constr8; "::"; c2 = constr8 -> <:ast< (CAST $c1 $c2) >> ] ]
  ;
  constr10:
    [ [ "!"; f = global; args = ne_constr9_list ->
          <:ast< (APPLISTEXPL $f ($LIST $args)) >>
      | f = constr9; args = ne_constr91_list ->
          <:ast< (APPLIST $f ($LIST $args)) >>
      | f = constr9 -> f ] ]
  ;
  ne_ident_comma_list:
    [ [ id = ident; ","; idl = ne_ident_comma_list -> id :: idl
      | id = ident -> [id] ] ]
  ;
  ident_comma_list_tail:
    [ [ ","; idl = ne_ident_comma_list -> idl
      | -> [] ] ]
  ;
  vardecls: (* This is interpreted by Pcoq.abstract_binder *)
    [ [ id = ident; idl = ident_comma_list_tail; c = type_option ->
          <:ast< (BINDER $c $id ($LIST $idl)) >>
      | id = ident; ":="; c = constr ->
	  <:ast< (LETIN $c $id) >>
      | id = ident; "="; c = constr ->
	  <:ast< (LETIN $c $id) >> ] ]
  ;
  ne_vardecls_list:
    [ [ id = vardecls; ";"; idl = ne_vardecls_list -> id :: idl
      | id = vardecls -> [id] ] ]
  ;
  binders:
    [ [ "["; bl = ne_vardecls_list; "]" -> bl ] ]
  ;
  ne_binders_list:
    [ [ bl = binders; bll = ne_binders_list -> bl @ bll
      | bl = binders -> bl ] ]
  ;
  type_option:
    [ [ ":"; c = constr -> c 
      | -> <:ast< (ISEVAR) >> ] ]
  ;
  constr91:
    [ [ n = Prim.number; "!"; c1 = constr9 ->
          <:ast< (EXPL $n $c1) >>
      | c1 = constr9 -> c1 ] ]
  ;
  ne_constr91_list:
    [ [ c1 = constr91; cl = ne_constr91_list -> c1::cl
      | c1 = constr91 -> [c1] ] ]
  ;
  ne_constr9_list:
    [ [ c1 = constr9; cl = ne_constr9_list -> c1::cl
      | c1 = constr9 -> [c1] ] ]
  ;
  fixbinder:
    [ [ id = ident; "/"; recarg = Prim.number; ":"; type_ = constr;
        ":="; def = constr -> <:ast< (NUMFDECL $id $recarg $type_ $def) >>
      | id = ident; idl = ne_binders_list; ":"; type_ = constr;
        ":="; def = constr ->
          <:ast< (FDECL $id (BINDERS ($LIST $idl)) $type_ $def) >> ] ]
  ;
  fixbinders:
    [ [ fb = fixbinder; "with"; fbs = fixbinders -> fb::fbs
      | fb = fixbinder -> [fb] ] ]
  ;
  cofixbinder:
    [ [ id = ident; ":"; type_ = constr; ":="; def = constr ->
          <:ast< (CFDECL $id $type_ $def) >> ] ]
  ;
  cofixbinders:
    [ [ fb = cofixbinder; "with"; fbs = cofixbinders -> fb::fbs
      | fb = cofixbinder -> [fb] ] ]
  ;
  product_tail:
    [ [ ";"; idl = ne_ident_comma_list;
        ":"; c = constr; c2 = product_tail ->
          <:ast< (PRODLIST $c ($SLAM $idl $c2)) >>
      | ";"; idl = ne_ident_comma_list; c2 = product_tail ->
          <:ast< (PRODLIST (ISEVAR) ($SLAM $idl $c2)) >>
      | ")"; c = constr -> c ] ]
  ;
END;;
