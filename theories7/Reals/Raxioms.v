(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*********************************************************)
(**    Axiomatisation of the classical reals             *)
(*********************************************************)

Require Export ZArith_base.
V7only [
Require Export Rsyntax.
Import R_scope.
].
Open Local Scope R_scope.

V7only [
(*********************************************************)
(*   Compatibility                                       *)
(*********************************************************)
Notation sumboolT := Specif.sumbool.
Notation leftT := Specif.left.
Notation rightT := Specif.right.
Notation sumorT := Specif.sumor.
Notation inleftT := Specif.inleft.
Notation inrightT := Specif.inright.
Notation sigTT := Specif.sigT.
Notation existTT := Specif.existT.
Notation SigT := Specif.sigT.
].

(*********************************************************)
(*               Field axioms                            *)
(*********************************************************)

(*********************************************************)
(**      Addition                                        *)
(*********************************************************)

(**********)
Axiom Rplus_sym:(r1,r2:R)``r1+r2==r2+r1``.
Hints Resolve Rplus_sym : real.

(**********)
Axiom Rplus_assoc:(r1,r2,r3:R)``(r1+r2)+r3==r1+(r2+r3)``.
Hints Resolve Rplus_assoc : real.

(**********)
Axiom Rplus_Ropp_r:(r:R)``r+(-r)==0``.
Hints Resolve Rplus_Ropp_r : real v62.

(**********)
Axiom Rplus_Ol:(r:R)``0+r==r``.
Hints Resolve Rplus_Ol : real.

(***********************************************************)       
(**       Multiplication                                   *)
(***********************************************************)

(**********)
Axiom Rmult_sym:(r1,r2:R)``r1*r2==r2*r1``.
Hints Resolve Rmult_sym : real v62. 

(**********)
Axiom Rmult_assoc:(r1,r2,r3:R)``(r1*r2)*r3==r1*(r2*r3)``.
Hints Resolve Rmult_assoc : real v62.

(**********)
Axiom Rinv_l:(r:R)``r<>0``->``(/r)*r==1``.
Hints Resolve Rinv_l : real.

(**********)
Axiom Rmult_1l:(r:R)``1*r==r``.
Hints Resolve Rmult_1l : real.

(**********)
Axiom R1_neq_R0:``1<>0``.
Hints Resolve R1_neq_R0 : real.

(*********************************************************)
(**      Distributivity                                  *)
(*********************************************************)

(**********)
Axiom Rmult_Rplus_distr:(r1,r2,r3:R)``r1*(r2+r3)==(r1*r2)+(r1*r3)``.
Hints Resolve Rmult_Rplus_distr : real v62.

(*********************************************************)
(**      Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(**      Total Order                                     *)
(*********************************************************)

(**********)
Axiom total_order_T:(r1,r2:R)(sumorT (sumboolT ``r1<r2`` r1==r2) ``r1>r2``).

(*********************************************************)
(**      Lower                                           *)
(*********************************************************)

(**********)
Axiom Rlt_antisym:(r1,r2:R)``r1<r2`` -> ~ ``r2<r1``.

(**********)
Axiom Rlt_trans:(r1,r2,r3:R)
  ``r1<r2``->``r2<r3``->``r1<r3``.

(**********)
Axiom Rlt_compatibility:(r,r1,r2:R)``r1<r2``->``r+r1<r+r2``.

(**********)
Axiom Rlt_monotony:(r,r1,r2:R)``0<r``->``r1<r2``->``r*r1<r*r2``.

Hints Resolve Rlt_antisym Rlt_compatibility Rlt_monotony : real.

(**********************************************************) 
(**      Injection from N to R                            *)
(**********************************************************)

(**********)
Fixpoint INR [n:nat]:R:=(Cases n of
                          O      => ``0``
                         |(S O)  => ``1``
                         |(S n)  => ``(INR n)+1``
                        end).  
Arguments Scope INR [nat_scope].


(**********************************************************) 
(**      Injection from [Z] to [R]                        *)
(**********************************************************)

(**********)
Definition IZR:Z->R:=[z:Z](Cases z of
                         ZERO      => ``0``
                        |(POS n) => (INR (convert n))
                        |(NEG n) => ``-(INR (convert n))``
                           end).  
Arguments Scope IZR [Z_scope].

(**********************************************************)
(**      [R] Archimedian                                  *)
(**********************************************************)

(**********)
Axiom archimed:(r:R)``(IZR (up r)) > r``/\``(IZR (up r))-r <= 1``.

(**********************************************************)
(**      [R] Complete                                     *)
(**********************************************************)

(**********)
Definition is_upper_bound:=[E:R->Prop][m:R](x:R)(E x)->``x <= m``.

(**********)
Definition bound:=[E:R->Prop](ExT [m:R](is_upper_bound E m)).

(**********)
Definition is_lub:=[E:R->Prop][m:R]
    (is_upper_bound E m)/\(b:R)(is_upper_bound E b)->``m <= b``.

(**********)
Axiom complet:(E:R->Prop)(bound E)->
              (ExT [x:R] (E x))->
              (sigTT R [m:R](is_lub E m)).

