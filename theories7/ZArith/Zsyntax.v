(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export BinInt.

V7only[

Grammar znatural ident :=
  nat_id [ prim:var($id) ] -> [$id]

with number :=

with negnumber := 

with formula : constr :=
  form_expr [ expr($p) ] -> [$p]
(*| form_eq [ expr($p) "=" expr($c) ] -> [ (eq Z $p $c) ]*)
| form_eq [ expr($p) "=" expr($c) ] -> [ (Coq.Init.Logic.eq ? $p $c) ]
| form_le [ expr($p) "<=" expr($c) ] -> [ (Zle $p $c) ]
| form_lt [ expr($p) "<" expr($c) ] -> [ (Zlt $p $c) ]
| form_ge [ expr($p) ">=" expr($c) ] -> [ (Zge $p $c) ]
| form_gt [ expr($p) ">" expr($c) ] -> [ (Zgt $p $c) ]
(*| form_eq_eq [ expr($p) "=" expr($c) "=" expr($c1) ]
              -> [ (eq Z $p $c)/\(eq Z $c $c1) ]*)
| form_eq_eq [ expr($p) "=" expr($c) "=" expr($c1) ]
              -> [ (Coq.Init.Logic.eq ? $p $c)/\(Coq.Init.Logic.eq ? $c $c1) ]
| form_le_le [ expr($p) "<=" expr($c) "<=" expr($c1) ]
              -> [ (Zle $p $c)/\(Zle $c $c1) ]
| form_le_lt [ expr($p) "<=" expr($c) "<" expr($c1) ]
              -> [ (Zle $p $c)/\(Zlt $c $c1) ]
| form_lt_le [ expr($p) "<" expr($c) "<=" expr($c1) ]
              -> [ (Zlt $p $c)/\(Zle $c $c1) ]
| form_lt_lt [ expr($p) "<" expr($c) "<" expr($c1) ]
              -> [ (Zlt $p $c)/\(Zlt $c $c1) ]
(*| form_neq  [ expr($p) "<>" expr($c) ] -> [  ~(Coq.Init.Logic.eq Z $p $c) ]*)
| form_neq  [ expr($p) "<>" expr($c) ] -> [  ~(Coq.Init.Logic.eq ? $p $c) ]
| form_comp [ expr($p) "?=" expr($c) ] -> [ (Zcompare $p $c) ]

with expr : constr :=
  expr_plus [ expr($p) "+" expr($c) ] -> [ (Zplus $p $c) ]
| expr_minus [ expr($p) "-" expr($c) ] -> [ (Zminus $p $c) ]
| expr2 [ expr2($e) ] -> [$e]

with expr2 : constr :=
  expr_mult [ expr2($p) "*" expr2($c) ] -> [ (Zmult $p $c) ]
| expr1 [ expr1($e) ] -> [$e]

with expr1 : constr :=
  expr_abs [ "|" expr($c) "|" ] -> [ (Zabs $c) ]
| expr0 [ expr0($e) ] -> [$e]

with expr0 : constr :=
  expr_id [ constr:global($c) ] -> [ $c ]
| expr_com [ "[" constr:constr($c) "]" ] -> [$c]
| expr_appl [ "(" application($a) ")" ] -> [$a]
| expr_num [ number($s) ] -> [$s ]
| expr_negnum [ "-" negnumber($n) ] -> [ $n ]
| expr_inv [ "-" expr0($c) ] -> [ (Zopp $c) ] 
| expr_meta [ zmeta($m) ] -> [ $m ]

with zmeta :=
| rimpl [ "?" ] -> [ ? ]
| rmeta0 [ "?" "0" ] -> [ ?0 ]
| rmeta1 [ "?" "1" ] -> [ ?1 ]
| rmeta2 [ "?" "2" ] -> [ ?2 ]
| rmeta3 [ "?" "3" ] -> [ ?3 ]
| rmeta4 [ "?" "4" ] -> [ ?4 ]
| rmeta5 [ "?" "5" ] -> [ ?5 ]

with application : constr :=
  apply [ application($p) expr($c1) ] -> [ ($p $c1) ]
| apply_inject_nat [ "inject_nat" constr:constr($c1) ] -> [ (inject_nat $c1) ]
| pair [ expr($p) "," expr($c) ] -> [ ($p, $c) ]
| appl0 [ expr($a) ] -> [$a]
.

Grammar constr constr0 :=
  z_in_com [ "`" znatural:formula($c) "`" ] -> [$c].

Grammar constr pattern :=
  z_in_pattern [ "`" prim:bigint($c) "`" ] -> [ 'Z: $c ' ].   

(* The symbols "`" "`" must be printed just once at the top of the expressions,
  to avoid printings like |``x` + `y`` < `45`| 
  for |x + y < 45|.
  So when a Z-expression is to be printed, its sub-expresssions are
  enclosed into an ast (ZEXPR \$subexpr), which is printed like \$subexpr
  but without symbols "`" "`" around. 

  There is just one problem: NEG and Zopp have the same printing rules.
  If Zopp is opaque, we may not be able to solve a goal like
  ` -5 = -5 ` by reflexivity. (In fact, this precise Goal is solved
  by the Reflexivity tactic, but more complex problems may arise 

  SOLUTION : Print (Zopp 5) for constants and -x for variables *)

Syntax constr
  level 0:
    Zle [ (Zle $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<= " (ZEXPR $n2) "`"]]
  | Zlt [ (Zlt $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "< " (ZEXPR $n2) "`" ]]
  | Zge [ (Zge $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] ">= " (ZEXPR $n2) "`" ]]
  | Zgt [ (Zgt $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "> " (ZEXPR $n2) "`" ]]
  | Zcompare [<<(Zcompare $n1 $n2)>>] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "?= " (ZEXPR $n2) "`" ]]
  | Zeq [ (eq Z $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "= " (ZEXPR $n2)"`"]]
  | Zneq [ ~(eq Z $n1 $n2) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<> " (ZEXPR $n2) "`"]]
  | Zle_Zle [ (Zle $n1 $n2)/\(Zle $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<= " (ZEXPR $n2)
                                [1 0] "<= " (ZEXPR $n3) "`"]]
  | Zle_Zlt [ (Zle $n1 $n2)/\(Zlt $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<= " (ZEXPR $n2)
                                [1 0] "< " (ZEXPR $n3) "`"]]
  | Zlt_Zle [ (Zlt $n1 $n2)/\(Zle $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "< " (ZEXPR $n2)
                                [1 0] "<= " (ZEXPR $n3) "`"]]
  | Zlt_Zlt [ (Zlt $n1 $n2)/\(Zlt $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "< " (ZEXPR $n2)
                                [1 0] "< " (ZEXPR $n3) "`"]]
  | ZZero_v7 [ ZERO ] -> [ "`0`" ]
  | ZPos_v7 [ (POS $r) ] -> [$r:"positive_printer":9]
  | ZNeg_v7 [ (NEG $r) ] -> [$r:"negative_printer":9]
  ;

  level 7:
    Zplus [ (Zplus $n1 $n2) ]
      -> [ [<hov 0> "`" (ZEXPR $n1):E "+"  [0 0] (ZEXPR $n2):L "`"] ]
  | Zminus [ (Zminus $n1 $n2) ]
      -> [ [<hov 0> "`" (ZEXPR $n1):E "-" [0 0] (ZEXPR $n2):L "`"] ]
  ;

  level 6:
    Zmult [ (Zmult $n1 $n2) ]
      -> [ [<hov 0> "`" (ZEXPR $n1):E "*" [0 0] (ZEXPR $n2):L "`"] ]
  ;

  level 8:
    Zopp [ (Zopp $n1) ] -> [ [<hov 0> "`" "-" (ZEXPR $n1):E "`"] ]
  | Zopp_POS [ (Zopp (POS $r)) ] -> 
         [ [<hov 0> "`(" "Zopp" [1 0] $r:"positive_printer_inside"  ")`"] ]
  | Zopp_ZERO [ (Zopp ZERO) ] -> [ [<hov 0> "`(" "Zopp" [1 0] "0" ")`"] ]
  | Zopp_NEG [ (Zopp (NEG $r)) ] ->  
         [ [<hov 0> "`(" "Zopp" [1 0] "(" $r:"negative_printer_inside" "))`"] ]
  ;

  level 4:
    Zabs [ (Zabs $n1) ] -> [  [<hov 0> "`|" (ZEXPR $n1):E "|`"] ]
  ;

  level 0:
    escape_inside [ << (ZEXPR $r) >> ] -> [ "[" $r:E "]" ]
  ;

  level 4:
    Zappl_inside [ << (ZEXPR (APPLIST $h ($LIST $t))) >> ]
      -> [ [<hov 0> "("(ZEXPR $h):E [1 0] (ZAPPLINSIDETAIL ($LIST $t)):E ")"] ]
  | Zappl_inject_nat [ << (ZEXPR (APPLIST <<inject_nat>> $n)) >> ]
      -> [ [<hov 0> "(inject_nat" [1 1] $n:L ")"] ]
  | Zappl_inside_tail [ << (ZAPPLINSIDETAIL $h ($LIST $t)) >> ]
      -> [(ZEXPR $h):E [1 0] (ZAPPLINSIDETAIL ($LIST $t)):E] 
  | Zappl_inside_one [ << (ZAPPLINSIDETAIL $e) >> ] ->[(ZEXPR $e):E]
  | pair_inside [ << (ZEXPR <<(pair $s1 $s2 $z1 $z2)>>) >> ] 
      -> [ [<hov 0> "("(ZEXPR $z1):E "," [1 0] (ZEXPR $z2):E ")"] ]
  ;

 level 3:
    var_inside [ << (ZEXPR ($VAR $i)) >> ] -> [$i]
  | secvar_inside [ << (ZEXPR (SECVAR $i)) >> ] -> [(SECVAR $i)]
  | const_inside [ << (ZEXPR (CONST $c)) >> ] -> [(CONST $c)]
  | mutind_inside [ << (ZEXPR (MUTIND $i $n)) >> ] 
      -> [(MUTIND $i $n)]
  | mutconstruct_inside [ << (ZEXPR (MUTCONSTRUCT $c1 $c2 $c3)) >> ]
      -> [ (MUTCONSTRUCT $c1 $c2 $c3) ]

  | O_inside [ << (ZEXPR << O >>) >> ] -> [ "O" ] (* To shunt Arith printer *)

  (* Added by JCF, 9/3/98; updated HH, 11/9/01 *)
  | implicit_head_inside [ << (ZEXPR (APPLISTEXPL ($LIST $c))) >> ]
      -> [ (APPLIST ($LIST $c)) ]
  | implicit_arg_inside  [ << (ZEXPR (EXPL "!" $n $c)) >> ] -> [ ]

  ;

  level 7:
    Zplus_inside
      [ << (ZEXPR <<(Zplus $n1 $n2)>>) >> ]
      	 -> [ (ZEXPR $n1):E "+" [0 0] (ZEXPR $n2):L ]
  | Zminus_inside
      [ << (ZEXPR <<(Zminus $n1 $n2)>>) >> ]
      	 -> [ (ZEXPR $n1):E "-" [0 0] (ZEXPR $n2):L ]
  ;

  level 6:
    Zmult_inside
      [ << (ZEXPR <<(Zmult $n1 $n2)>>) >> ]
      	 -> [ (ZEXPR $n1):E "*" [0 0] (ZEXPR $n2):L ]
  ;

  level 5:
    Zopp_inside [ << (ZEXPR <<(Zopp $n1)>>) >> ] -> [ "(-" (ZEXPR $n1):E ")" ]
  ;  

  level 10:
    Zopp_POS_inside [ << (ZEXPR <<(Zopp (POS $r))>>) >> ] -> 
      	 [ [<hov 0> "Zopp" [1 0] $r:"positive_printer_inside" ] ]
  | Zopp_ZERO_inside [ << (ZEXPR <<(Zopp ZERO)>>) >> ] -> 
      	 [ [<hov 0> "Zopp" [1 0] "0"] ]
  | Zopp_NEG_inside [ << (ZEXPR <<(Zopp (NEG $r))>>) >> ] ->  
      	 [ [<hov 0> "Zopp" [1 0] $r:"negative_printer_inside" ] ]
  ;

  level 4:
    Zabs_inside [ << (ZEXPR <<(Zabs $n1)>>) >> ] -> [ "|" (ZEXPR $n1) "|"]
  ;

  level 0:
    ZZero_inside [ << (ZEXPR <<ZERO>>) >> ] -> ["0"]
  | ZPos_inside [ << (ZEXPR <<(POS $p)>>) >>] -> 
      [$p:"positive_printer_inside":9]
  | ZNeg_inside [ << (ZEXPR <<(NEG $p)>>) >>] ->
      [$p:"negative_printer_inside":9]
.
].

V7only[
(* For parsing/printing based on scopes *)
Module Z_scope.

Infix LEFTA 4 "+" Zplus : Z_scope.
Infix LEFTA 4 "-" Zminus : Z_scope.
Infix LEFTA 3 "*" Zmult : Z_scope.
Notation "- x" := (Zopp x) (at level 0): Z_scope V8only.
Infix NONA 5 "<=" Zle : Z_scope.
Infix NONA 5 "<"  Zlt : Z_scope.
Infix NONA 5 ">=" Zge : Z_scope.
Infix NONA 5 ">"  Zgt  : Z_scope.
Infix NONA 5 "?=" Zcompare : Z_scope.
Notation "x <= y <= z" := (Zle x y)/\(Zle y z)
  (at level 5, y at level 4):Z_scope
  V8only (at level 70, y at next level).
Notation "x <= y < z"  := (Zle x y)/\(Zlt y z)
  (at level 5, y at level 4):Z_scope
  V8only (at level 70, y at next level).
Notation  "x < y < z"  := (Zlt x y)/\(Zlt y z)
  (at level 5, y at level 4):Z_scope
  V8only (at level 70, y at next level).
Notation  "x < y <= z" := (Zlt x y)/\(Zle y z)
  (at level 5, y at level 4):Z_scope
  V8only (at level 70, y at next level).
Notation  "x = y = z" := x=y/\y=z : Z_scope
  V8only (at level 70, y at next level).

(* Now a polymorphic notation
Notation "x <> y" := ~(eq Z x y) (at level 5, no associativity) : Z_scope.
*)

(* Notation "| x |" (Zabs x) : Z_scope.(* "|" conflicts with THENS *)*)

(* Overwrite the printing of "`x = y`" *)
Syntax constr level 0:
  Zeq [ (eq Z $n1 $n2) ] -> [[<hov 0> $n1 [1 0] "= " $n2 ]].

Open Scope Z_scope.

End Z_scope.
].
