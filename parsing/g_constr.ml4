
(* $Id$ *)

open Pcoq
open Constr

GEXTEND Gram
  GLOBAL: ident constr0 constr1 constr2 constr3 lassoc_constr4 constr5
          constr6 constr7 constr8 constr9 constr10 lconstr constr
          ne_ident_comma_list ne_constr_list;

  ident:
    [ [ id = IDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  raw_constr:
    [ [ c = Prim.ast -> c ] ]
  ;
  constr:
    [ [ c = constr8 -> c ] ]
  ;
  lconstr:
    [ [ c = constr10 -> c ] ]
  ;
  ne_constr_list:
    [ [ c1 = constr; cl = ne_constr_list -> c1::cl
      | c1 = constr -> [c1] ] ]
  ;
  constr0:
    [ [ "?" -> <:ast< (ISEVAR) >>
      | "?"; n = Prim.number -> <:ast< (META $n) >>
      | "["; id1 = IDENT; ":"; c = constr; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST $c [$id1]$c2) >>
      | "["; id1 = IDENT; ","; idl = ne_ident_comma_list;
        ":"; c = constr; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST $c [$id1]($SLAM $idl $c2)) >>
      | "["; id1 = IDENT; ","; idl = ne_ident_comma_list;
             c = abstraction_tail ->
          <:ast< (LAMBDALIST (ISEVAR) [$id1]($SLAM $idl $c)) >>
      | "["; id1 = IDENT; c = abstraction_tail ->
          <:ast< (LAMBDALIST (ISEVAR) [$id1]$c) >>
      | "["; id1 = IDENT; "="; c = constr; "]"; c2 = constr ->
          <:ast< (ABST #Core#let.cci $c [$id1]$c2) >> 
      | "<<"; id1 = IDENT; ">>"; c = constr -> <:ast< [$id1]$c >>
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
(*
      | "("; lc1 = lconstr; ")"; "@"; "["; cl = ne_constr_list; "]" ->
          <:ast< (XTRA"$SOAPP" $lc1 ($LIST $cl)) >>
*)
      | "Prop" -> <:ast< (PROP) >>
      | "Set"  -> <:ast< (SET) >>
      | "Type" -> <:ast< (TYPE) >>
      | IDENT "Fix"; id = ident; "{"; fbinders = fixbinders; "}" ->
          <:ast< (FIX $id ($LIST $fbinders)) >>
      | IDENT "CoFix"; id = ident; "{"; fbinders = cofixbinders; "}" ->
          <:ast< (COFIX $id ($LIST $fbinders)) >>
      | v = ident -> v ] ]
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
      | IDENT "let"; id1 = IDENT ; "="; c = constr; "in";
        c1 = constr -> <:ast< (ABST #Core#let.cci $c [$id1]$c1) >>
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
  constr2:
    [ [ c = constr1 -> c ] ]
  ;
  constr3:
    [ [ c1 = constr2 -> c1 ] ]
  ;
  lassoc_constr4:
    [ [ c1 = constr3 -> c1 ] ]
  ;
  constr5:
    [ [ c1 = lassoc_constr4 -> c1
      | c1 = lassoc_constr4; "::"; c2 = constr5 ->
          <:ast< (CAST $c1 $c2) >> ] ]
  ;
  constr6:
    [ [ c1 = constr5 -> c1 ] ]
  ;
  constr7:
    [ RIGHTA [ c1 = constr6 -> c1 ] ]
  ;
  constr8:
    [ [ c1 = constr7 -> c1
      | c1 = constr7; "->"; c2 = constr8 ->
          <:ast< (PROD $c1 [<>]$c2) >> ] ]
  ;
  constr9:
    [ [ c1 = constr8 -> c1 ] ]
  ;
  constr10:
    [ [ "!"; f = IDENT; args = ne_constr9_list ->
          <:ast< (APPLISTEXPL ($VAR $f) ($LIST $args)) >>
      | f = constr9; args = ne_constr91_list ->
          <:ast< (APPLIST $f ($LIST $args)) >>
      | f = constr9 -> f ] ]
  ;
  ne_ident_comma_list:
    [ [ id = ident; ","; idl = ne_ident_comma_list -> id::idl
      | id = ident -> [id] ] ]
  ;
  binder:
    [ [ idl = ne_ident_comma_list; c = type_option ->
          <:ast< (BINDER $c ($LIST $idl)) >> ] ]
  ;
  ne_binder_list:
    [ [ id = binder; ";"; idl = ne_binder_list -> id::idl
      | id = binder -> [id] ] ]
  ;
  type_option:
    [ [ ":"; c = constr -> c 
      | -> <:ast< (ISEVAR) >> ] ]
  ;
(*  parameters:
    [ [ "["; bl = ne_binder_semi_list; "]" -> $bl ] ]
  ;
  parameters_list:
    [ [ 
          <:ast< (BINDERLIST ($LIST $bl)) >>
      |  -> <:ast< (BINDERLIST) >> ] ]
  ;
*)  constr91:
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
      | id = ident; "["; idl = ne_binder_list; "]"; ":"; type_ = constr;
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
  abstraction_tail:
    [ [ ";"; idl = ne_ident_comma_list;
        ":"; c = constr; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST $c ($SLAM $idl $c2)) >>
      | ";"; idl = ne_ident_comma_list; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST (ISEVAR) ($SLAM $idl $c2)) >>
      | "]"; c = constr -> c ] ]
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
