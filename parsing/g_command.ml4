
(* $Id$ *)

open Pcoq

open Command

GEXTEND Gram
  ident:
    [ [ id = IDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  raw_command:
    [ [ c = Prim.ast -> c ] ]
  ;
  command:
    [ [ c = command8 -> c ] ]
  ;
  lcommand:
    [ [ c = command10 -> c ] ]
  ;
  ne_command_list:
    [ [ c1 = command; cl = ne_command_list -> c1::cl
      | c1 = command -> [c1] ] ]
  ;
  command0:
    [ [ "?" -> <:ast< (XTRA "ISEVAR") >>
      | "?"; n = Prim.number -> <:ast< (META $n) >>
      | "["; id1 = IDENT; ":"; c = command; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST $c [$id1]$c2) >>
      | "["; id1 = IDENT; ","; idl = ne_ident_comma_list;
        ":"; c = command; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST $c [$id1]($SLAM $idl $c2)) >>
      | "["; id1 = IDENT; ","; idl = ne_ident_comma_list;
             c = abstraction_tail ->
          <:ast< (LAMBDALIST (XTRA "ISEVAR") [$id1]($SLAM $idl $c)) >>
      | "["; id1 = IDENT; c = abstraction_tail ->
          <:ast< (LAMBDALIST (XTRA "ISEVAR") [$id1]$c) >>
      | "["; id1 = IDENT; "="; c = command; "]"; c2 = command ->
          <:ast< (ABST #Core#let.cci $c [$id1]$c2) >> 
      | "<<"; id1 = IDENT; ">>"; c = command -> <:ast< [$id1]$c >>
      | "("; lc1 = lcommand; ":"; c = command; body = product_tail ->
          let id = Ast.coerce_to_var "lc1" lc1 in
            <:ast< (PROD $c [$id]$body) >>
      | "("; lc1 = lcommand; ","; lc2 = lcommand; ":"; c = command; 
        body = product_tail ->
          let id1 = Ast.coerce_to_var "lc1" lc1 in
          let id2 = Ast.coerce_to_var "lc2" lc2 in
            <:ast< (PRODLIST $c [$id1][$id2]$body) >>
      | "("; lc1 = lcommand; ","; lc2 = lcommand; ",";
        idl = ne_ident_comma_list; ":"; c = command; body = product_tail ->
          let id1 = Ast.coerce_to_var "lc1" lc1 in
          let id2 = Ast.coerce_to_var "lc2" lc2 in
            <:ast< (PRODLIST $c [$id1][$id2]($SLAM $idl $body)) >>
      | "("; lc1 = lcommand; ")" -> lc1
      | "("; lc1 = lcommand; ")"; "@"; "["; cl = ne_command_list; "]" ->
          <:ast< (XTRA"$SOAPP" $lc1 ($LIST $cl)) >>
      | "Prop" -> <:ast< (PROP {Null}) >>
      | "Set" -> <:ast< (PROP {Pos}) >>
      | "Type" -> <:ast< (TYPE) >>
      | IDENT "Fix"; id = ident; "{"; fbinders = fixbinders; "}" ->
          <:ast< (FIX $id ($LIST $fbinders)) >>
      | IDENT "CoFix"; id = ident; "{"; fbinders = cofixbinders; "}" ->
          <:ast< (COFIX $id ($LIST $fbinders)) >>
      | v = ident -> v ] ]
  ;
  command1:
    [ [ "<"; ":"; IDENT "ast"; ":"; "<"; c = raw_command; ">>" -> c
      | "<"; l1 = lcommand; ">"; IDENT "Match"; c = command; "with";
        cl = ne_command_list; "end" ->
          <:ast< (XTRA "REC" $l1 $c ($LIST $cl)) >>
      | "<"; l1 = lcommand; ">"; IDENT "Match"; c = command; "with"; "end"
        ->
          <:ast< (XTRA "REC" $l1 $c) >>
      | "<"; l1 = lcommand; ">"; IDENT "Case"; c = command; "of";
        cl = ne_command_list; "end" ->
          <:ast< (MUTCASE $l1 $c ($LIST $cl)) >>
      | "<"; l1 = lcommand; ">"; IDENT "Case"; c = command; "of"; "end" ->
          <:ast< (MUTCASE $l1 $c) >>
      | IDENT "Case"; c = command; "of"; cl = ne_command_list; "end" ->
          <:ast< (XTRA "MLCASE" "NOREC" $c ($LIST $cl)) >>
      | IDENT "Case"; c = command; "of"; "end" ->
          <:ast< (XTRA "MLCASE" "NOREC" $c) >>
      | IDENT "Match"; c = command; "with"; cl = ne_command_list; "end" ->
          <:ast< (XTRA "MLCASE" "REC" $c ($LIST $cl)) >>
      | IDENT "let"; "("; b = ne_ident_comma_list; ")"; "=";
        c = command; "in"; c1 = command ->
          <:ast< (XTRA "MLCASE" "NOREC" $c (LAMBDALIST (XTRA "ISEVAR")
                   ($SLAM $b $c1))) >>
      | IDENT "let"; id1 = IDENT ; "="; c = command; "in";
        c1 = command -> <:ast< (ABST #Core#let.cci $c [$id1]$c1) >>
      | IDENT "if"; c1 = command; IDENT "then"; c2 = command;
        IDENT "else"; c3 = command ->
        <:ast< ( XTRA "MLCASE" "NOREC" $c1 $c2 $c3) >>
(* EN ATTENTE DE REMPLACER CE QUI EST DANS Program.v ... *)
      | "<"; l1 = lcommand; ">";
        IDENT "let"; "("; b = ne_ident_comma_list; ")"; "=";
        c = command; "in"; c1 = command ->
         <:ast< (MUTCASE $l1 $c (LAMBDALIST (XTRA "ISEVAR") ($SLAM $b $c1))) >>
      | "<"; l1 = lcommand; ">";
        IDENT "if"; c1 = command; IDENT "then";
        c2 = command; IDENT "else"; c3 = command ->
          <:ast< (MUTCASE $l1 $c1 $c2 $c3) >>
      | c = command0 -> c ] ]
  ;
  command2:
    [ [ c = command1 -> c ] ]
  ;
  command3:
    [ [ c1 = command2 -> c1 ] ]
  ;
  lassoc_command4:
    [ [ c1 = command3 -> c1 ] ]
  ;
  command5:
    [ [ c1 = lassoc_command4 -> c1
      | c1 = lassoc_command4; "::"; c2 = command5 ->
          <:ast< (CAST $c1 $c2) >> ] ]
  ;
  command6:
    [ [ c1 = command5 -> c1 ] ]
  ;
  command7:
    [ RIGHTA [ c1 = command6 -> c1 ] ]
  ;
  command8:
    [ [ c1 = command7 -> c1
      | c1 = command7; "->"; c2 = command8 ->
          <:ast< (PROD $c1 [<>]$c2) >> ] ]
  ;
  command9:
    [ [ c1 = command8 -> c1 ] ]
  ;
  command10:
    [ [ "!"; f = IDENT; args = ne_command9_list ->
          <:ast< (APPLIST (XTRA "!" ($VAR $f)) ($LIST $args)) >>
      | f = command9; args = ne_command91_list ->
          <:ast< (APPLIST $f ($LIST $args)) >>
      | f = command9 -> f ] ]
  ;
  ne_ident_comma_list:
    [ [ id = ident; ","; idl = ne_ident_comma_list -> id::idl
      | id = ident -> [id] ] ]
  ;
  binder:
    [ [ idl = ne_ident_comma_list; ":"; c = command ->
          <:ast< (BINDER $c ($LIST $idl)) >> ] ]
  ;
  ne_binder_list:
    [ [ id = binder; ";"; idl = ne_binder_list -> id::idl
      | id = binder -> [id] ] ]
  ;
  command91:
    [ [ n = Prim.number; "!"; c1 = command9 ->
          <:ast< (XTRA "!" $n $c1) >>
      | c1 = command9 -> c1 ] ]
  ;
  ne_command91_list:
    [ [ c1 = command91; cl = ne_command91_list -> c1::cl
      | c1 = command91 -> [c1] ] ]
  ;
  ne_command9_list:
    [ [ c1 = command9; cl = ne_command9_list -> c1::cl
      | c1 = command9 -> [c1] ] ]
  ;
  fixbinder:
    [ [ id = ident; "/"; recarg = Prim.number; ":"; type_ = command;
        ":="; def = command -> <:ast< (NUMFDECL $id $recarg $type_ $def) >>
      | id = ident; "["; idl = ne_binder_list; "]"; ":"; type_ = command;
        ":="; def = command ->
          <:ast< (FDECL $id (BINDERS ($LIST $idl)) $type_ $def) >> ] ]
  ;
  fixbinders:
    [ [ fb = fixbinder; "with"; fbs = fixbinders -> fb::fbs
      | fb = fixbinder -> [fb] ] ]
  ;
  cofixbinder:
    [ [ id = ident; ":"; type_ = command; ":="; def = command ->
          <:ast< (CFDECL $id $type_ $def) >> ] ]
  ;
  cofixbinders:
    [ [ fb = cofixbinder; "with"; fbs = cofixbinders -> fb::fbs
      | fb = cofixbinder -> [fb] ] ]
  ;
  abstraction_tail:
    [ [ ";"; idl = ne_ident_comma_list;
        ":"; c = command; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST $c ($SLAM $idl $c2)) >>
      | ";"; idl = ne_ident_comma_list; c2 = abstraction_tail ->
          <:ast< (LAMBDALIST (XTRA "ISEVAR") ($SLAM $idl $c2)) >>
      | "]"; c = command -> c ] ]
  ;
  product_tail:
    [ [ ";"; idl = ne_ident_comma_list;
        ":"; c = command; c2 = product_tail ->
          <:ast< (PRODLIST $c ($SLAM $idl $c2)) >>
      | ";"; idl = ne_ident_comma_list; c2 = product_tail ->
          <:ast< (PRODLIST (XTRA "ISEVAR") ($SLAM $idl $c2)) >>
      | ")"; c = command -> c ] ]
  ;
END
