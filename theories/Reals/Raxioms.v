
(* $Id$ *)

(*********************************************************)
(*           Axiomatisation of the classical reals       *)
(*                                                       *)
(*********************************************************)

Require Export ZArith.
Require Export Rsyntax.
Require Export TypeSyntax.

(*********************************************************)
(*       Field axioms                                   *)
(*********************************************************)
(*********************************************************)
(*       Addition                                        *)
(*********************************************************)

(**********)
Axiom Rplus_sym:(r1,r2:R)``r1+r2==r2+r1``.

(**********)
Axiom Rplus_assoc:(r1,r2,r3:R)``(r1+r2)+r3==r1+(r2+r3)``.

(**********)
Axiom Rplus_Ropp_r:(r:R)``r+(-r)==0``.
Hints Resolve Rplus_Ropp_r : real v62.

(**********)
Axiom Rplus_ne:(r:R)``r+0==r``/\``0+r==r``.
Hints Resolve Rplus_ne : real v62.

(***********************************************************)       
(*        Multiplication                                   *)
(***********************************************************)

(**********)
Axiom Rmult_sym:(r1,r2:R)``r1*r2==r2*r1``.
Hints Resolve Rmult_sym : real v62. 

(**********)
Axiom Rmult_assoc:(r1,r2,r3:R)``(r1*r2)*r3==r1*(r2*r3)``.
Hints Resolve Rmult_assoc : real v62.

(**********)
Axiom Rinv_l:(r:R)``r<>0``->``(1/r)*r==1``.

(**********)
Axiom Rmult_ne:(r:R)``r*1==r``/\``1*r==r``.
Hints Resolve Rmult_ne : real v62.

(**********)
Axiom R1_neq_R0:(~R1==R0).

(*********************************************************)
(*       Distributivity                                  *)
(*********************************************************)

(**********)
Axiom Rmult_Rplus_distr:(r1,r2,r3:R)``r1*(r2+r3)==(r1*r2)+(r1*r3)``.
Hints Resolve Rmult_Rplus_distr : real v62.

(*********************************************************)
(*       Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(*       Total Order                                     *)
(*********************************************************)

(**********)
Axiom total_order_T:(r1,r2:R)(sumorT (sumboolT ``r1<r2`` r1==r2) ``r1>r2``).

(*********************************************************)
(*       Lower                                           *)
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

(**********************************************************) 
(*       Injection from N to R                            *)
(**********************************************************)

(**********)
Fixpoint INR [n:nat]:R:=(Cases n of
                          O      => R0
                         |(S O)  => R1 
                         |(S n)  => (Rplus (INR n) R1)
                        end).  

(**********************************************************) 
(*       Injection from Z to R                            *)
(**********************************************************)

(**********)
Definition IZR:Z->R:=[z:Z](Cases z of
                         ZERO      => R0
                        |(POS n) => (INR (convert n))
                        |(NEG n) => (Ropp (INR (convert n)))
                           end).  

(**********************************************************)
(*       R Archimedian                                    *)
(**********************************************************)

(**********)
Axiom archimed:(r:R)``(IZR (up r)) > r``/\``(IZR (up r))-r <= 1``.

(**********************************************************)
(*       R Complete                                        *)
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

