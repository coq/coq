
(* $Id$ *)

Require Export Datatypes.

(* Parsing of things in Datatypes.v *)

Grammar command command1 :=
  pair_expl [ "<" lcommand($l1) "," lcommand($c2) ">" "(" lcommand($c3) ","
    lcommand($c4) ")" ] -> [<<(pair $l1 $c2 $c3 $c4)>>]
| fst_expl [ "<" lcommand($l1) "," lcommand($c2) ">" "Fst" "("
    lcommand($l) ")" ] -> [<<(fst $l1 $c2 $l)>>]
| snd_expl [ "<" lcommand($l1) "," lcommand($c2) ">" "Snd" "("
    lcommand($l) ")" ] -> [<<(snd $l1 $c2 $l)>>]

with command0 :=
  pair [ "(" lcommand($lc1) "," lcommand($lc2) ")" ] ->
         [<<(pair ? ? $lc1 $lc2)>>]

with command3 :=
  prod [ command2($c1) "*" command3($c2) ] -> [<<(prod $c1 $c2)>>].

(* Pretty-printing of things in Datatypes.v *)

Syntax constr
  level 4:
    sum [<<(sum $t1 $t2)>>] -> [ [<hov 0> $t1:E [0 1] "+" $t2:L ] ]
  ;

  level 3:
    product [<<(prod $t1 $t2)>>] -> [ [<hov 0>  $t1:L [0 1] "*" $t2:E ] ]
  ;

  level 1:
    pair
      [<<(pair $_ $_ $t3 $t4)>>] -> [ [<hov 0> "(" $t3:E ","[0 1] $t4:E ")" ] ]
  | fst_imp [<<(fst $_ $_ $t2)>>] -> [ [<hov 0> "(Fst " $t2:E ")"] ]
  | snd_imp [<<(snd $_ $_ $t2)>>] -> [ [<hov 0> "(Snd " $t2:E ")"] ].
