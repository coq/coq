
(* $Id$ *)

Require Logic_Type.

(* Parsing of things in Logic_type.v *)

Grammar command command1 :=
  eqT_expl [ "<" lcommand($l1) ">" command0($c1) "==" command0($c2) ] ->
          [<<(eqT $l1 $c1 $c2)>>]
| eqT_impl [ command0($c) "==" command0($c2) ] -> [<<(eqT ? $c $c2)>>]
| idT_expl [ "<" lcommand($l1) ">" command0($c1) "===" command0($c2) ] ->
          [<<(identityT $l1 $c1 $c2)>>]
| idT_impl [ command0($c) "===" command0($c2) ] -> [<<(identityT ? $c $c2)>>]

with command10 :=
  allTexplicit [ "ALLT" ident($v) ":" command($t) "|" command($c1) ]
                          -> [<<(allT $t [$v : $t]$c1)>>]
| allTimplicit [ "ALLT" ident($v) "|" command($c1) ] 
                          -> [<<(allT ? [$v]$c1)>>]
| exTexplicit [ "EXT" ident($v) ":" command($t) "|" command($c1) ]
                          -> [<<(exT $t [$v : $t]$c1)>>]
| exTimplicit [ "EXT" ident($v) "|" command($c1) ] 
                          -> [<<(exT ? [$v]$c1)>>]
| exT2explicit [ "EXT" ident($v) ":" command($t) "|" command($c1) "&"
           command($c2) ] -> [<<(exT2 $t [$v : $t]$c1 [$v : $t]$c2)>>]
| exT2implicit [ "EXT" ident($v) "|" command($c1) "&" 
           command($c2) ] -> [<<(exT2 ? [$v]$c1 [$v]$c2)>>].

(* Pretty-printing of things in Logic_type.v *)

Syntax constr
  level 10:
    allT_pred [ (allT $_ $p) ] -> [ [<hov 0> "AllT " $p:L ] ]
  | allT [ (allT $T [$x : $T]$p) ]
       -> [ [<hov 3> "ALLT " $x ":" $T:L " |" [1 0] $p:L ] ]

  | exT_pred [ (exT $_ $p) ] -> [ [<hov 4> "ExT " $p:L ] ]
  | exT [ (exT $t1 [$x : $T]$p) ] 
       -> [ [<hov 4> "EXT " $x ":" $T:L " |" [1 0] $p:L ] ]

  | exT2_pred [ (exT2 $_ $p1 $p2) ]
       -> [ [<hov 4> "ExT2 " $p1:L [1 0] $p2:L ] ]
  | exT2 [ (exT2 $T [$x : $T]$P1 [$x : $T]$P2) ] 
       -> [ [<hov 2> "EXT " $x ":" $T:L " |" [1 2] $P1:L [1 0] "& " $P2:L] ]
  ;

  level 1:
    eqT [ (eqT $_ $c1 $c2) ] -> [ [<hov 1> $c1:E [0 0] "==" $c2:E ] ]

  | identityT [ (identityT $_ $c1 $c2) ]
       -> [ [<hov 1> $c1:E [0 0] "===" $c2:E ] ].
