
(* $Id$ *)

Require Export Logic.

(* Parsing of things in Logic.v *)

Grammar constr constr1 :=
  conj [ "<" lconstr($l1) "," lconstr($c2) ">" "{" constr($c3) ","
        constr($c4) "}" ] -> [ (conj $l1 $c2 $c3 $c4) ]
| proj1 [ "<" lconstr($l1) "," lconstr($c2) ">" "Fst" "{"
        lconstr($l) "}" ] -> [ (proj1 $l1 $c2 $l) ]
| proj2 [ "<" lconstr($l1) "," lconstr($c2) ">" "Snd" "{"
        lconstr($l) "}" ] -> [ (proj2 $l1 $c2 $l) ]
| IF [ "either" constr($c) "and_then" constr($t) "or_else" constr($e) ] ->
       [ (IF $c $t $e) ]
| all [ "<" lconstr($l1) ">" "All" "(" lconstr($l2) ")" ] ->
       [ (all $l1 $l2) ]
| eq_expl [ "<" lconstr($l1) ">" constr0($c1) "=" constr0($c2) ] ->
            [ (eq $l1 $c1 $c2) ]
| eq_impl [ constr0($c) "=" constr0($c2) ] -> [ (eq ? $c $c2) ]

with constr2 :=
  not [ "~" constr2($c) ] -> [ (not $c) ]

with constr6 :=
  and [ constr5($c1) "/\\" constr6($c2) ] -> [ (and $c1 $c2) ]

with constr7 :=
  or [ constr6($c1) "\\/" constr7($c2) ] -> [ (or $c1 $c2) ]

with constr8 :=
  iff [ constr7($c1) "<->" constr8($c2) ] -> [ (iff $c1 $c2) ]

with constr10 :=
  allexplicit [ "ALL" ident($x) ":" constr($t) "|" constr($p) ]
                          -> [ (all $t [$x : $t]$p) ]
| allimplicit [ "ALL" ident($x) "|" constr($p) ]
                          -> [ (all ? [$x]$p) ]
| exexplicit [ "EX" ident($v) ":" constr($t) "|" constr($c1) ]
                          -> [ (ex $t [$v : $t]$c1) ]
| eximplicit [ "EX" ident($v) "|" constr($c1) ] 
                          -> [ (ex ? [$v]$c1) ]
| ex2explicit [ "EX" ident($v) ":" constr($t) "|" constr($c1) "&"
           constr($c2) ] -> [ (ex2 $t [$v : $t]$c1 [$v : $t]$c2) ]
| ex2implicit [ "EX" ident($v) "|" constr($c1) "&" 
           constr($c2) ] -> [ (ex2 ? [$v]$c1 [$v]$c2) ].


(* Pretty-printing of things in Logic.v *)

Syntax constr
  level 1:
    equal [ (eq $_  $t1  $t2) ] -> [ [<hov 0> $t1:E [0 1]  "=" $t2:E ] ]
  | conj [ (conj $t1 $t2 $t3 $t4) ]
      -> [ [<hov 1> [<hov 1> "<" $t1:L "," [0 0] $t2:L ">" ] [0 0]
                    [<hov 1> "{" $t3:L "," [0 0] $t4:L "}"] ] ]
  | IF [ either $c and_then $t or_else $e ]
      -> [ [<hov 0> "either" [1 1] $c:E
                [<hov 0> [1 1] "and_then" [1 1] $t:E ]
                [<hov 0> [1 1] "or_else" [1 1] $e:E ]] ]
  ;

  level 2:
    not [ ~ $t1 ] -> [ [<hov 0> "~" $t1:E ] ]
  ;

  level 6:
    and [ $t1 /\ $t2 ] -> [ [<hov 0> $t1:L [0 0] "/\\" $t2:E ] ]
  ;

  level 7:
    or [ $t1 \/ $t2 ] -> [ [<hov 0> $t1:L [0 0]  "\\/" $t2:E ] ]
  ;

  level 8:
    iff [ $t1 <-> $t2 ] -> [ [<hov 0> $t1:L [0 0] "<->" $t2:E ] ]
  ;

  level 10:
    all_pred [ (all $_ $p) ] -> [ [<hov 4> "All " $p:L ] ]
  | all_imp [ (all $_ [$x : $T]$t) ]
       -> [ [<hov 3> "ALL " $x ":" $T:L " |" [1 0] $t:L ] ]

  | ex_pred [ (ex $_ $p) ] -> [ [<hov 0> "Ex " $p:L ] ]
  | ex [ (ex $_ [$x : $T]$P) ] 
       -> [ [<hov 2> "EX " $x ":" $T:L " |" [1 0] $P:L ] ]

  | ex2_pred [ (ex2 $_ $p1 $p2) ]
       -> [ [<hov 3> "Ex2 " $p1:L [1 0] $p2:L ] ]
  | ex2 [ (ex2 $_ [$x : $T]$P1 [$x : $T]$P2) ] 
       -> [ [<hov 2> "EX " $x ":" $T:L " |" [1 2] $P1:L [1 0] "& " $P2:L] ].
