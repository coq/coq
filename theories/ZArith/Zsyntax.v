(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export fast_integer.
Require Export zarith_aux.

Axiom My_special_variable0 : positive->positive.
Axiom My_special_variable1 : positive->positive.

Grammar znatural ident :=
  nat_id [ prim:var($id) ] -> [$id]

with number :=

with negnumber := 

with formula : constr :=
  form_expr [ expr($p) ] -> [$p]
| form_eq [ expr($p) "=" expr($c) ] -> [ (eq Z $p $c) ]
| form_le [ expr($p) "<=" expr($c) ] -> [ (Zle $p $c) ]
| form_lt [ expr($p) "<" expr($c) ] -> [ (Zlt $p $c) ]
| form_ge [ expr($p) ">=" expr($c) ] -> [ (Zge $p $c) ]
| form_gt [ expr($p) ">" expr($c) ] -> [ (Zgt $p $c) ]
| form_eq_eq [ expr($p) "=" expr($c) "=" expr($c1) ]
              -> [ (eq Z $p $c)/\(eq Z $c $c1) ]
| form_le_le [ expr($p) "<=" expr($c) "<=" expr($c1) ]
              -> [ (Zle $p $c)/\(Zle $c $c1) ]
| form_le_lt [ expr($p) "<=" expr($c) "<" expr($c1) ]
              -> [ (Zle $p $c)/\(Zlt $c $c1) ]
| form_lt_le [ expr($p) "<" expr($c) "<=" expr($c1) ]
              -> [ (Zlt $p $c)/\(Zle $c $c1) ]
| form_lt_lt [ expr($p) "<" expr($c) "<" expr($c1) ]
              -> [ (Zlt $p $c)/\(Zlt $c $c1) ]
| form_neq  [ expr($p) "<>" expr($c) ] -> [  ~(eq Z $p $c) ]
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

with application : constr :=
  apply [ application($p) expr($c1) ] -> [ ($p $c1) ]
| apply_inject_nat [ "inject_nat" constr:constr($c1) ] -> [ (inject_nat $c1) ]
| pair [ expr($p) "," expr($c) ] -> [ ($p, $c) ]
| appl0 [ expr($a) ] -> [$a]
.

Grammar constr constr0 :=
  z_in_com [ "`" znatural:formula($c) "`" ] -> [$c].

Grammar constr pattern :=
  z_in_pattern [ "`" znatural:number($c) "`" ] -> [$c].   

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
    My_special_variable0 [ My_special_variable0 ] -> [ "POS" ]
  | My_special_variable1 [ My_special_variable1 ] -> [ "NEG" ] 
  | Zle [ (Zle $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<= " (ZEXPR $n2) "`"]]
  | Zlt [ (Zlt $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "< "(ZEXPR $n2) "`" ]]
  | Zge [ (Zge $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] ">= "(ZEXPR $n2) "`" ]]
  | Zgt [ (Zgt $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "> "(ZEXPR $n2) "`" ]]
  | Zcompare [<<(Zcompare $n1 $n2)>>] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "?= " (ZEXPR $n2) "`" ]]
  | Zeq [ (eq Z $n1 $n2) ] -> 
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "= "(ZEXPR $n2)"`"]]
  | Zneq [ ~(eq Z $n1 $n2) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<> "(ZEXPR $n2) "`"]]
  | Zle_Zle [ (Zle $n1 $n2)/\(Zle $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<= " (ZEXPR $n2)
                                [1 0] "<= " (ZEXPR $n3) "`"]]
  | Zle_Zlt [ (Zle $n1 $n2)/\(Zlt $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "<= "(ZEXPR $n2)
                                [1 0] "< " (ZEXPR $n3) "`"]]
  | Zlt_Zle [ (Zlt $n1 $n2)/\(Zle $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "< " (ZEXPR $n2)
                                [1 0] "<= " (ZEXPR $n3) "`"]]
  | Zlt_Zlt [ (Zlt $n1 $n2)/\(Zlt $n2 $n3) ] ->
      [[<hov 0> "`" (ZEXPR $n1) [1 0] "< " (ZEXPR $n2)
                                [1 0] "< " (ZEXPR $n3) "`"]]
  | ZZero [ ZERO ] -> ["`0`"]
  | ZPos [ (POS $r) ] -> [$r:"positive_printer"]
  | ZNeg [ (NEG $r) ] -> [$r:"negative_printer"]
  ;

  level 7:
    Zplus [ (Zplus $n1 $n2) ]
      -> [ [<hov 0> "`"(ZEXPR $n1):E "+"  [0 0] (ZEXPR $n2):L "`"] ]
  | Zminus [ (Zminus $n1 $n2) ]
      -> [ [<hov 0> "`"(ZEXPR $n1):E "-" [0 0] (ZEXPR $n2):L "`"] ]
  ;

  level 6:
    Zmult [ (Zmult $n1 $n2) ]
      -> [ [<hov 0> "`"(ZEXPR $n1):E "*" [0 0] (ZEXPR $n2):L "`"] ]
  ;

  level 8:
    Zopp [ (Zopp $n1) ] -> [ [<hov 0> "`" "-"(ZEXPR $n1):E "`"] ]
  | Zopp_POS [ (Zopp (POS $r)) ] -> 
         [ [<hov 0> "`(" "Zopp" [1 0] $r:"positive_printer_inside"  ")`"] ]
  | Zopp_ZERO [ (Zopp ZERO) ] -> [ [<hov 0> "`(" "Zopp" [1 0] "0" ")`"] ]
  | Zopp_NEG [ (Zopp (NEG $r)) ] ->  
         [ [<hov 0> "`(" "Zopp" [1 0] "(" $r:"negative_printer_inside" "))`"] ]
  ;

  level 4:
    Zabs [ (Zabs $n1) ] -> [  [<hov 0> "`|"(ZEXPR $n1):E "|`"] ]
  ;

  level 0:
    escape_inside [ << (ZEXPR $r) >> ] -> [ "[" $r:E "]" ]
  ;

  level 4:
    Zappl_inside [ << (ZEXPR (APPLIST $h ($LIST $t))) >> ]
      -> [ [<hov 0> "("(ZEXPR $h):E [1 0] (APPLINSIDETAIL ($LIST $t)):E ")"] ]
  | Zappl_inject_nat [ << (ZEXPR (APPLIST <<inject_nat>> $n)) >> ]
      -> [ (APPLIST <<inject_nat>> $n) ]
  | Zappl_inside_tail [ << (APPLINSIDETAIL $h ($LIST $t)) >> ]
      -> [(ZEXPR $h):E [1 0] (APPLINSIDETAIL ($LIST $t)):E] 
  | Zappl_inside_one [ << (APPLINSIDETAIL $e) >> ] ->[(ZEXPR $e):E]
  | pair_inside [ << (ZEXPR <<(pair $s1 $s2 $z1 $z2)>>) >> ] 
      -> [ [<hov 0> "("(ZEXPR $z1):E "," [1 0] (ZEXPR $z2):E ")"] ]
  ;

 level 3:
    var_inside [ << (ZEXPR ($VAR $i)) >> ] -> [$i]
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
  | ZPos_inside [ << (ZEXPR <<(POS $p)>>) >>] -> [$p:"positive_printer_inside"]
  | ZNeg_inside [ << (ZEXPR <<(NEG $p)>>) >> ] -> 
      	       	       	  [$p:"negative_printer_inside"].
