(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i $Id$ i*)

Require Export Rdefinitions.

Axiom NRplus : R->R.
Axiom NRmult : R->R.

V7only[
Grammar rnatural ident :=
  nat_id [ prim:var($id) ] -> [$id]

with rnegnumber : constr := 
  neg_expr [ "-" rnumber ($c) ] -> [ (Ropp $c) ] 

with rnumber :=

with rformula : constr :=
  form_expr [ rexpr($p) ] -> [ $p ]
(* | form_eq [ rexpr($p) "==" rexpr($c) ] -> [ (eqT R $p $c) ] *)
| form_eq [ rexpr($p) "==" rexpr($c) ] -> [ (eqT ? $p $c) ]
| form_eq2 [ rexpr($p) "=" rexpr($c) ] -> [ (eqT ? $p $c) ]
| form_le [ rexpr($p) "<=" rexpr($c) ] -> [ (Rle $p $c) ]
| form_lt [ rexpr($p) "<" rexpr($c) ] -> [ (Rlt $p $c) ]
| form_ge [ rexpr($p) ">=" rexpr($c) ] -> [ (Rge $p $c) ]
| form_gt [ rexpr($p) ">" rexpr($c) ] -> [ (Rgt $p $c) ]
(*
| form_eq_eq [ rexpr($p) "==" rexpr($c) "==" rexpr($c1) ]
              -> [ (eqT R $p $c)/\(eqT R $c $c1) ]
*)
| form_eq_eq [ rexpr($p) "==" rexpr($c) "==" rexpr($c1) ]
              -> [ (eqT ? $p $c)/\(eqT ? $c $c1) ]
| form_le_le [ rexpr($p) "<=" rexpr($c) "<=" rexpr($c1) ]
              -> [ (Rle $p $c)/\(Rle $c $c1) ]
| form_le_lt [ rexpr($p) "<=" rexpr($c) "<" rexpr($c1) ]
              -> [ (Rle $p $c)/\(Rlt $c $c1) ]
| form_lt_le [ rexpr($p) "<" rexpr($c) "<=" rexpr($c1) ]
              -> [ (Rlt $p $c)/\(Rle $c $c1) ]
| form_lt_lt [ rexpr($p) "<" rexpr($c) "<" rexpr($c1) ]
              -> [ (Rlt $p $c)/\(Rlt $c $c1) ]
| form_neq  [ rexpr($p) "<>" rexpr($c) ] -> [ ~(eqT ? $p $c) ]

with rexpr : constr :=
  expr_plus [ rexpr($p) "+" rexpr($c) ] -> [ (Rplus $p $c) ]
| expr_minus [ rexpr($p) "-" rexpr($c) ] -> [ (Rminus $p $c) ]
| rexpr2 [ rexpr2($e) ] -> [ $e ]

with rexpr2 : constr :=
  expr_mult [ rexpr2($p) "*" rexpr2($c) ] -> [ (Rmult $p $c) ]
| rexpr0 [ rexpr0($e) ] -> [ $e ]


with rexpr0 : constr :=
  expr_id [ constr:global($c) ] -> [ $c ]
| expr_com [ "[" constr:constr($c) "]" ] -> [ $c ]
| expr_appl [ "(" rapplication($a) ")" ] -> [ $a ]
| expr_num [ rnumber($s) ] -> [ $s ]
| expr_negnum [ "-" rnegnumber($n) ] -> [ $n ]
| expr_div [ rexpr0($p) "/" rexpr0($c) ] -> [ (Rdiv $p $c) ]
| expr_opp [ "-" rexpr0($c) ] -> [ (Ropp $c) ] 
| expr_inv [ "/" rexpr0($c) ] -> [ (Rinv $c) ]
| expr_meta [ meta($m) ] -> [ $m ]

with meta :=
| rimpl [ "?" ] -> [ ? ]
| rmeta0 [ "?" "0" ] -> [ ?0 ]
| rmeta1 [ "?" "1" ] -> [ ?1 ]
| rmeta2 [ "?" "2" ] -> [ ?2 ]
| rmeta3 [ "?" "3" ] -> [ ?3 ]
| rmeta4 [ "?" "4" ] -> [ ?4 ]
| rmeta5 [ "?" "5" ] -> [ ?5 ]

with rapplication : constr :=
  apply [ rapplication($p) rexpr($c1) ] -> [ ($p $c1) ]
| pair [ rexpr($p) "," rexpr($c) ] -> [ ($p, $c) ]
| appl0 [ rexpr($a) ] -> [ $a ].

Grammar constr constr0 :=
  r_in_com [ "``" rnatural:rformula($c) "``" ] -> [ $c ].

Grammar constr atomic_pattern :=
  r_in_pattern [ "``" rnatural:rnumber($c) "``" ] -> [ $c ].   

(*i* pp **)

Syntax constr
  level 0:
   Rle [ (Rle $n1 $n2) ] -> 
      [[<hov 0> "``" (REXPR $n1) [1 0] "<= " (REXPR $n2) "``"]]
  | Rlt [ (Rlt $n1 $n2) ] -> 
      [[<hov 0> "``" (REXPR $n1) [1 0] "< "(REXPR $n2) "``" ]]
  | Rge [ (Rge $n1 $n2) ] -> 
      [[<hov 0> "``" (REXPR $n1) [1 0] ">= "(REXPR $n2) "``" ]]
  | Rgt [ (Rgt $n1 $n2) ] -> 
      [[<hov 0> "``" (REXPR $n1) [1 0] "> "(REXPR $n2) "``" ]]
  | Req [ (eqT R $n1 $n2) ] -> 
      [[<hov 0> "``" (REXPR $n1) [1 0] "= "(REXPR $n2)"``"]]
  | Rneq [ ~(eqT R $n1 $n2) ] ->
      [[<hov 0> "``" (REXPR $n1) [1 0] "<> "(REXPR $n2) "``"]]
  | Rle_Rle [ (Rle $n1 $n2)/\(Rle $n2 $n3) ] ->
      [[<hov 0> "``" (REXPR $n1) [1 0] "<= " (REXPR $n2)
                                [1 0] "<= " (REXPR $n3) "``"]]
  | Rle_Rlt [ (Rle $n1 $n2)/\(Rlt $n2 $n3) ] ->
      [[<hov 0> "``" (REXPR $n1) [1 0] "<= "(REXPR $n2)
                                [1 0] "< " (REXPR $n3) "``"]]
  | Rlt_Rle [ (Rlt $n1 $n2)/\(Rle $n2 $n3) ] ->
      [[<hov 0> "``" (REXPR $n1) [1 0] "< " (REXPR $n2)
                                [1 0] "<= " (REXPR $n3) "``"]]
  | Rlt_Rlt [ (Rlt $n1 $n2)/\(Rlt $n2 $n3) ] ->
      [[<hov 0> "``" (REXPR $n1) [1 0] "< " (REXPR $n2)
                                [1 0] "< " (REXPR $n3) "``"]]
  | Rzero [ R0 ] -> [ "``0``" ]
  | Rone [ R1 ] -> [ "``1``" ]
  ;

  level 7:
    Rplus [ (Rplus $n1 $n2) ]
      -> [ [<hov 0> "``"(REXPR $n1):E "+"  [0 0] (REXPR $n2):L "``"] ]
   | Rodd_outside [(Rplus R1 $r)] -> [ $r:"r_printer_odd_outside"]
   | Rminus [ (Rminus $n1 $n2) ]
      -> [ [<hov 0> "``"(REXPR $n1):E "-" [0 0] (REXPR $n2):L "``"] ]
  ;

  level 6:
    Rmult [ (Rmult $n1 $n2) ]
      -> [ [<hov 0> "``"(REXPR $n1):E "*" [0 0] (REXPR $n2):L "``"] ]
    | Reven_outside [ (Rmult (Rplus R1 R1) $r) ] -> [ $r:"r_printer_even_outside"]
    | Rdiv [ (Rdiv $n1 $n2) ]
      -> [ [<hov 0> "``"(REXPR $n1):E "/" [0 0] (REXPR $n2):L "``"] ]
  ;

  level 8:
    Ropp [(Ropp $n1)] -> [ [<hov 0> "``" "-"(REXPR $n1):E "``"] ]
    | Rinv [(Rinv $n1)] -> [ [<hov 0> "``" "/"(REXPR $n1):E "``"] ]
  ;

  level 0:
    rescape_inside [<< (REXPR $r) >>] -> [ "[" $r:E "]" ]
  ;

  level 4:
    Rappl_inside [<<(REXPR (APPLIST $h ($LIST $t)))>>]
 -> [ [<hov 0> "("(REXPR $h):E [1 0] (RAPPLINSIDETAIL ($LIST $t)):E ")"] ]
  | Rappl_inside_tail [<<(RAPPLINSIDETAIL $h ($LIST $t))>>]
      -> [(REXPR $h):E [1 0] (RAPPLINSIDETAIL ($LIST $t)):E] 
  | Rappl_inside_one [<<(RAPPLINSIDETAIL $e)>>] ->[(REXPR $e):E]
  | rpair_inside [<<(REXPR <<(pair $s1 $s2 $r1 $r2)>>)>>] 
      -> [ [<hov 0> "("(REXPR $r1):E "," [1 0] (REXPR $r2):E ")"] ]
  ;

 level 3:
    rvar_inside [<<(REXPR ($VAR $i))>>] -> [$i]
  | rsecvar_inside [<<(REXPR (SECVAR $i))>>] -> [(SECVAR $i)]
  | rconst_inside [<<(REXPR (CONST $c))>>] -> [(CONST $c)]
  | rmutind_inside [<<(REXPR (MUTIND $i $n))>>] 
      -> [(MUTIND $i $n)]
  | rmutconstruct_inside [<<(REXPR (MUTCONSTRUCT $c1 $c2 $c3))>>]
      -> [ (MUTCONSTRUCT $c1 $c2 $c3) ]
  | rimplicit_head_inside [<<(REXPR (XTRA "!" $c))>>] -> [ $c ]
  | rimplicit_arg_inside  [<<(REXPR (XTRA "!" $n $c))>>] -> [ ]

  ;

  
  level 7:
   Rplus_inside
      [<<(REXPR <<(Rplus $n1 $n2)>>)>>]
      	 -> [ (REXPR $n1):E "+" [0 0] (REXPR $n2):L ]
  | Rminus_inside
      [<<(REXPR <<(Rminus $n1 $n2)>>)>>]
      	 -> [ (REXPR $n1):E "-" [0 0] (REXPR $n2):L ]
  | NRplus_inside
      [<<(REXPR <<(NRplus $r)>>)>>] -> [ "(" "1" "+" (REXPR $r):L ")"]
  ;

  level 6:
    Rmult_inside
      [<<(REXPR <<(Rmult $n1 $n2)>>)>>]
      	 -> [ (REXPR $n1):E "*" (REXPR $n2):L ]
  |  NRmult_inside
      [<<(REXPR <<(NRmult $r)>>)>>] -> [ "(" "2" "*" (REXPR $r):L ")"]
  ;

  level 5:
    Ropp_inside [<<(REXPR <<(Ropp $n1)>>)>>] -> [ " -" (REXPR $n1):E  ]
  | Rinv_inside [<<(REXPR <<(Rinv $n1)>>)>>] -> [ "/" (REXPR $n1):E  ]
  | Rdiv_inside
      [<<(REXPR <<(Rdiv $n1 $n2)>>)>>]
      	 -> [ (REXPR $n1):E "/" [0 0] (REXPR $n2):L ]
  ;  

  level 0:
    Rzero_inside [<<(REXPR <<R0>>)>>] -> ["0"]
  | Rone_inside [<<(REXPR <<R1>>)>>] -> ["1"]
  | Rodd_inside [<<(REXPR <<(Rplus R1 $r)>>)>>] -> [ $r:"r_printer_odd" ]
  | Reven_inside [<<(REXPR <<(Rmult (Rplus R1 R1) $r)>>)>>] -> [ $r:"r_printer_even" ]
.

(* For parsing/printing based on scopes *)
Module R_scope.

Infix "<=" Rle (at level 5, no associativity) : R_scope V8only.
Infix "<"  Rlt (at level 5, no associativity) : R_scope V8only.
Infix ">=" Rge (at level 5, no associativity) : R_scope V8only.
Infix ">" Rgt (at level 5, no associativity) : R_scope V8only.
Infix "+" Rplus (at level 4) : R_scope V8only.
Infix "-" Rminus (at level 4) : R_scope V8only.
Infix "*" Rmult (at level 3) : R_scope V8only.
Infix "/" Rdiv (at level 3) : R_scope V8only.
Notation "- x" := (Ropp x) (at level 0) : R_scope V8only.
Notation "x == y == z" := (eqT R x y)/\(eqT R y z)
  (at level 5, y at level 4, no associtivity): R_scope.
Notation "x <= y <= z" := (Rle x y)/\(Rle y z)
  (at level 5, y at level 4) : R_scope
  V8only.
Notation "x <= y < z" := (Rle x y)/\(Rlt y z)
  (at level 5, y at level 4) : R_scope
  V8only.
Notation "x < y < z" := (Rlt x y)/\(Rlt y z)
  (at level 5, y at level 4) : R_scope
  V8only.
Notation "x < y <= z" := (Rlt x y)/\(Rle y z)
  (at level 5, y at level 4) : R_scope
  V8only.
Notation "/ x" := (Rinv x) (at level 0): R_scope
  V8only.

Open Local Scope R_scope.
End R_scope.
].
