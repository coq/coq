(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*********************************************************)
(*s    {Axiomatisation of the classical reals}           *)
(*********************************************************)

Require Export ZArith.
Require Export Rsyntax.
Require Export TypeSyntax.

(*********************************************************)
(*              {Field axioms}                           *)
(*********************************************************)
(*********************************************************)
(*s      Addition                                        *)
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
(*s       Multiplication                                   *)
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
(*s      Distributivity                                  *)
(*********************************************************)

(**********)
Axiom Rmult_Rplus_distr:(r1,r2,r3:R)``r1*(r2+r3)==(r1*r2)+(r1*r3)``.
Hints Resolve Rmult_Rplus_distr : real v62.

(*********************************************************)
(*       Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(*s      Total Order                                     *)
(*********************************************************)

(**********)
Axiom total_order_T:(r1,r2:R)(sumorT (sumboolT ``r1<r2`` r1==r2) ``r1>r2``).

(*********************************************************)
(*s      Lower                                           *)
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
(*s      Injection from N to R                            *)
(**********************************************************)

(**********)
Fixpoint INR [n:nat]:R:=(Cases n of
                          O      => ``0``
                         |(S O)  => ``1``
                         |(S n)  => ``(INR n)+1``
                        end).  

(**********************************************************) 
(*s      Injection from Z to R                            *)
(**********************************************************)

(**********)
Definition IZR:Z->R:=[z:Z](Cases z of
                         ZERO      => ``0``
                        |(POS n) => (INR (convert n))
                        |(NEG n) => ``-(INR (convert n))``
                           end).  

(**********************************************************)
(*s      R Archimedian                                    *)
(**********************************************************)

(**********)
Axiom archimed:(r:R)``(IZR (up r)) > r``/\``(IZR (up r))-r <= 1``.

(**********************************************************)
(*s      R Complete                                        *)
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
              (ExT [m:R](is_lub E m)).

