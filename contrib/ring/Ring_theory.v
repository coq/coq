(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Export Bool.

Implicit Arguments On.

Grammar ring formula : constr :=
  formula_expr [ expr($p) ] -> [$p]
| formula_eq [ expr($p) "==" expr($c) ] -> [ (eqT A $p $c) ]

with expr : constr :=
  RIGHTA
    expr_plus [ expr($p) "+" expr($c) ] -> [ (Aplus $p $c) ]
  | expr_expr1 [ expr1($p) ] -> [$p]

with expr1 : constr :=
  RIGHTA
    expr1_plus [ expr1($p) "*" expr1($c) ] -> [ (Amult $p $c) ]
  | expr1_final [ final($p) ] -> [$p]

with final : constr :=
  final_var [ prim:var($id) ] -> [ $id ]
| final_constr [ "[" constr:constr($c) "]" ] -> [ $c ]
| final_app [ "(" application($r) ")" ] -> [ $r ]
| final_0 [ "0" ] -> [ Azero ]
| final_1 [ "1" ] -> [ Aone ]
| final_uminus [ "-" expr($c) ] -> [ (Aopp $c) ]

with application : constr :=
  LEFTA
    app_cons [ application($p) application($c1) ] -> [ ($p $c1) ]
  | app_tail [ expr($c1) ] -> [ $c1 ].

Grammar constr constr0 :=
  formula_in_constr [ "[" "|" ring:formula($c) "|" "]" ] -> [ $c ].

Section Theory_of_semi_rings.

Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
(* There is also a "weakly decidable" equality on A. That means 
  that if (A_eq x y)=true then x=y but x=y can arise when 
  (A_eq x y)=false. On an abstract ring the function [x,y:A]false
  is a good choice. The proof of A_eq_prop is in this case easy. *)
Variable Aeq : A -> A -> bool.

Record Semi_Ring_Theory : Prop :=
{ SR_plus_sym  : (n,m:A)[| n + m == m + n |];
  SR_plus_assoc : (n,m,p:A)[| n + (m + p) == (n + m) + p |];

  SR_mult_sym : (n,m:A)[| n*m == m*n |];
  SR_mult_assoc : (n,m,p:A)[| n*(m*p) == (n*m)*p |];
  SR_plus_zero_left :(n:A)[| 0 + n == n|];
  SR_mult_one_left : (n:A)[| 1*n == n |];
  SR_mult_zero_left : (n:A)[| 0*n == 0 |];
  SR_distr_left   : (n,m,p:A) [| (n + m)*p == n*p + m*p |];
  SR_plus_reg_left : (n,m,p:A)[| n + m == n + p |] -> m==p;
  SR_eq_prop : (x,y:A) (Is_true (Aeq x y)) -> x==y
}.

Variable T : Semi_Ring_Theory.

Local plus_sym  := (SR_plus_sym T).
Local plus_assoc := (SR_plus_assoc T).
Local mult_sym  := ( SR_mult_sym T).
Local mult_assoc := (SR_mult_assoc T).
Local plus_zero_left := (SR_plus_zero_left T).
Local mult_one_left := (SR_mult_one_left T). 
Local mult_zero_left := (SR_mult_zero_left T).
Local distr_left := (SR_distr_left T).
Local plus_reg_left := (SR_plus_reg_left T).

Hints Resolve  plus_sym  plus_assoc  mult_sym mult_assoc plus_zero_left
  mult_one_left mult_zero_left distr_left plus_reg_left.

(* Lemmas whose form is x=y are also provided in form y=x because Auto does
  not symmetry *) 
Lemma SR_mult_assoc2 : (n,m,p:A)[| (n * m) * p == n * (m * p) |].
Symmetry; EAuto. Save.

Lemma SR_plus_assoc2 : (n,m,p:A)[| (n + m) + p == n + (m + p) |].
Symmetry; EAuto. Save.

Lemma SR_plus_zero_left2 : (n:A)[| n == 0 + n |].
Symmetry; EAuto. Save.

Lemma SR_mult_one_left2 : (n:A)[| n == 1*n |].
Symmetry; EAuto. Save.

Lemma SR_mult_zero_left2 : (n:A)[| 0 == 0*n |].
Symmetry; EAuto. Save.

Lemma SR_distr_left2 : (n,m,p:A) [| n*p + m*p  == (n + m)*p |].
Symmetry; EAuto. Save.

Lemma SR_plus_permute : (n,m,p:A)[| n + (m + p) == m + (n + p) |].
Intros.
Rewrite -> plus_assoc.
Elim (plus_sym m n).
Rewrite <- plus_assoc.
Reflexivity.
Save.

Lemma SR_mult_permute : (n,m,p:A) [| n*(m*p) == m*(n*p) |].
Intros.
Rewrite -> mult_assoc.
Elim (mult_sym m n).
Rewrite <- mult_assoc.
Reflexivity.
Save.

Hints Resolve SR_plus_permute SR_mult_permute.

Lemma SR_distr_right : (n,m,p:A) [|  n*(m + p) == (n*m) + (n*p) |].
Intros.
Repeat Rewrite -> (mult_sym n).
EAuto.
Save.

Lemma SR_distr_right2 : (n,m,p:A) [|  (n*m) + (n*p) == n*(m + p) |].
Symmetry; Apply SR_distr_right. Save.

Lemma SR_mult_zero_right : (n:A)[|  n*0 == 0|].
Intro; Rewrite mult_sym; EAuto.
Save.

Lemma SR_mult_zero_right2 : (n:A)[| 0 == n*0 |].
Intro; Rewrite mult_sym; EAuto.
Save.

Lemma SR_plus_zero_right :(n:A)[| n + 0 == n |].
Intro; Rewrite plus_sym; EAuto.
Save.
Lemma SR_plus_zero_right2 :(n:A)[| n == n + 0 |].
Intro; Rewrite plus_sym; EAuto.
Save.

Lemma SR_mult_one_right : (n:A)[| n*1 == n |].
Intro; Elim mult_sym; Auto.
Save.

Lemma SR_mult_one_right2 : (n:A)[| n == n*1 |].
Intro; Elim mult_sym; Auto.
Save.

Lemma SR_plus_reg_right : (n,m,p:A)[| m + n == p + n |] -> m==p.
Intros n m p; Rewrite (plus_sym m n); Rewrite (plus_sym p n); EAuto.
Save.

End Theory_of_semi_rings.

Section Theory_of_rings.

Variable A : Type.

Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.


Record Ring_Theory : Prop :=
{ Th_plus_sym  : (n,m:A)[| n + m == m + n |];
  Th_plus_assoc : (n,m,p:A)[| n + (m + p) == (n + m) + p |];
  Th_mult_sym : (n,m:A)[| n*m == m*n |];
  Th_mult_assoc : (n,m,p:A)[| n*(m*p) == (n*m)*p |];
  Th_plus_zero_left :(n:A)[| 0 + n == n|];
  Th_mult_one_left : (n:A)[| 1*n == n |];
  Th_opp_def : (n:A) [| n + (-n) == 0 |];
  Th_distr_left   : (n,m,p:A) [| (n + m)*p == n*p + m*p |];
  Th_eq_prop : (x,y:A) (Is_true (Aeq x y)) -> x==y
}.

Variable T : Ring_Theory.

Local plus_sym  := (Th_plus_sym T).
Local plus_assoc := (Th_plus_assoc T).
Local mult_sym  := ( Th_mult_sym T).
Local mult_assoc := (Th_mult_assoc T).
Local plus_zero_left := (Th_plus_zero_left T).
Local mult_one_left := (Th_mult_one_left T). 
Local opp_def := (Th_opp_def T).
Local distr_left := (Th_distr_left T).

Hints Resolve plus_sym plus_assoc mult_sym mult_assoc plus_zero_left mult_one_left
  opp_def distr_left.

(* Lemmas whose form is x=y are also provided in form y=x because Auto does
  not symmetry *) 
Lemma Th_mult_assoc2 : (n,m,p:A)[| (n * m) * p == n * (m * p) |].
Symmetry; EAuto. Save.

Lemma Th_plus_assoc2 : (n,m,p:A)[| (n + m) + p == n + (m + p) |].
Symmetry; EAuto. Save.

Lemma Th_plus_zero_left2 : (n:A)[| n == 0 + n |].
Symmetry; EAuto. Save.

Lemma Th_mult_one_left2 : (n:A)[| n == 1*n |].
Symmetry; EAuto. Save.

Lemma Th_distr_left2 : (n,m,p:A) [| n*p + m*p  == (n + m)*p |].
Symmetry; EAuto. Save.

Lemma Th_opp_def2 : (n:A) [| 0 == n + (-n) |].
Symmetry; EAuto. Save.

Lemma Th_plus_permute : (n,m,p:A)[| n + (m + p) == m + (n + p) |].
Intros.
Rewrite -> plus_assoc.
Elim (plus_sym m n).
Rewrite <- plus_assoc.
Reflexivity.
Save.

Lemma Th_mult_permute : (n,m,p:A) [| n*(m*p) == m*(n*p) |].
Intros.
Rewrite -> mult_assoc.
Elim (mult_sym m n).
Rewrite <- mult_assoc.
Reflexivity.
Save.

Hints Resolve Th_plus_permute Th_mult_permute.

Lemma aux1 : (a:A) [| a + a == a |] -> [| a == 0 |].
Intros.
Generalize (opp_def a).
Pattern 1 a.
Rewrite <- H.
Rewrite <- plus_assoc.
Rewrite -> opp_def.
Elim plus_sym.
Rewrite plus_zero_left.
Trivial.
Save.

Lemma Th_mult_zero_left :(n:A)[| 0*n == 0 |].
Intros.
Apply aux1.
Rewrite <- distr_left.
Rewrite plus_zero_left.
Reflexivity.
Save.
Hints Resolve Th_mult_zero_left.

Lemma Th_mult_zero_left2 : (n:A)[| 0 == 0*n |].
Symmetry; EAuto. Save.

Lemma aux2 : (x,y,z:A) [|x+y==0|] -> [|x+z==0|] -> y==z.
Intros.
Rewrite <- (plus_zero_left y).
Elim H0.
Elim plus_assoc.
Elim (plus_sym y z).
Rewrite -> plus_assoc.
Rewrite -> H.
Rewrite plus_zero_left.
Reflexivity.
Save.

Lemma Th_opp_mult_left : (x,y:A)[| -(x*y) == (-x)*y |].
Intros.
Apply (aux2 1![|x*y|]);
[ Apply opp_def
| Rewrite <- distr_left;
  Rewrite -> opp_def;
  Auto].
Save.
Hints Resolve Th_opp_mult_left.

Lemma Th_opp_mult_left2 : (x,y:A)[| (-x)*y == -(x*y)  |].
Symmetry; EAuto. Save.

Lemma Th_mult_zero_right : (n:A)[|  n*0 == 0|].
Intro; Elim mult_sym; EAuto.
Save.

Lemma Th_mult_zero_right2 : (n:A)[| 0 == n*0 |].
Intro; Elim mult_sym; EAuto.
Save.

Lemma Th_plus_zero_right :(n:A)[| n + 0 == n |].
Intro; Rewrite plus_sym; EAuto.
Save.

Lemma Th_plus_zero_right2 :(n:A)[| n == n + 0 |].
Intro; Rewrite plus_sym; EAuto.
Save.

Lemma Th_mult_one_right : (n:A)[| n*1 == n |].
Intro;Elim mult_sym; EAuto.
Save.

Lemma Th_mult_one_right2  : (n:A)[| n == n*1 |].
Intro;Elim mult_sym; EAuto.
Save.

Lemma Th_opp_mult_right : (x,y:A)[| -(x*y) == x*(-y) |].
Intros; Do 2 Rewrite -> (mult_sym x); Auto.
Save.

Lemma Th_opp_mult_right2 : (x,y:A)[| x*(-y) == -(x*y) |].
Intros; Do 2 Rewrite -> (mult_sym x); Auto.
Save.

Lemma Th_plus_opp_opp : (x,y:A)[| (-x) + (-y) == -(x+y) |].
Intros.
Apply (aux2 1![| x + y |]);
[ Elim plus_assoc;
  Rewrite -> (Th_plus_permute y [| -x |]); Rewrite -> plus_assoc;
  Rewrite -> opp_def;  Rewrite plus_zero_left; Auto
| Auto ].
Save.

Lemma Th_plus_permute_opp: (n,m,p:A)[| (-m) + (n + p) == n + ((-m)+p) |].
EAuto. Save.

Lemma Th_opp_opp : (n:A)[| -(-n) == n |].
Intro; Apply (aux2 1![| -n |]); 
  [ Auto | Elim plus_sym; Auto ].
Save.
Hints Resolve Th_opp_opp.

Lemma Th_opp_opp2 : (n:A)[| n == -(-n) |].
Symmetry; EAuto. Save.

Lemma Th_mult_opp_opp : (x,y:A)[| (-x)*(-y) == x*y |].
Intros; Rewrite <- Th_opp_mult_left; Rewrite <- Th_opp_mult_right; Auto.
Save.

Lemma Th_mult_opp_opp2 : (x,y:A)[| x*y == (-x)*(-y) |].
Symmetry; Apply Th_mult_opp_opp. Save.

Lemma Th_opp_zero : [| -0 == 0 |].
Rewrite <- (plus_zero_left [| -0 |]).
Auto. Save.

Lemma Th_plus_reg_left : (n,m,p:A)[| n + m == n + p |] -> m==p.
Intros; Generalize (congr_eqT ? ? [z][| (-n)+z |] ? ? H).
Repeat Rewrite plus_assoc.
Rewrite (plus_sym [| -n |] n).
Rewrite opp_def.
Repeat Rewrite Th_plus_zero_left; EAuto.
Save.

Lemma Th_plus_reg_right : (n,m,p:A)[| m + n == p + n |] -> m==p.
Intros.
EApply Th_plus_reg_left with n. 
Rewrite (plus_sym n m).
Rewrite (plus_sym n p).
Auto.
Save.

Lemma Th_distr_right : (n,m,p:A) [|  n*(m + p) == (n*m) + (n*p) |].
Intros.
Repeat Rewrite -> (mult_sym n).
EAuto.
Save.

Lemma Th_distr_right2  : (n,m,p:A) [| (n*m) + (n*p) == n*(m + p)  |].
Symmetry; Apply Th_distr_right.
Save.

End Theory_of_rings.

Hints Resolve Th_mult_zero_left Th_plus_reg_left : core.

Implicit Arguments Off.

Definition Semi_Ring_Theory_of :
  (A:Type)(Aplus : A -> A -> A)(Amult : A -> A -> A)(Aone : A)
  (Azero : A)(Aopp : A -> A)(Aeq : A -> A -> bool)
  (Ring_Theory Aplus Amult Aone Azero Aopp Aeq)
    ->(Semi_Ring_Theory Aplus Amult Aone Azero Aeq).
Destruct 1.
Split; Intros; Simpl; EAuto.
Defined.

(* Every ring can be viewed as a semi-ring : this property will be used
  in Abstract_polynom. *)
Coercion Semi_Ring_Theory_of : Ring_Theory >-> Semi_Ring_Theory.


Section product_ring.

End product_ring.

Section power_ring.

End power_ring.
