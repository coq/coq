
(* $Id$ *)

(*********************************************************)
(*           Axiomatisation of the classical reals       *)
(*                                                       *)
(*********************************************************)

Require Export ZArith.
Require Export TypeSyntax.

Parameter R:Type.
Parameter R0:R.
Parameter R1:R.
Parameter Rplus:R->R->R.
Parameter Rmult:R->R->R.
Parameter Ropp:R->R.
Parameter Rinv:R->R. 
Parameter Rlt:R->R->Prop.    
Parameter up:R->Z.
(*********************************************************)

(**********)
Definition Rgt:R->R->Prop:=[r1,r2:R](Rlt r2 r1).

(**********)
Definition Rle:R->R->Prop:=[r1,r2:R]((Rlt r1 r2)\/(r1==r2)).

(**********)
Definition Rge:R->R->Prop:=[r1,r2:R]((Rgt r1 r2)\/(r1==r2)).

(**********)
Definition Rminus:R->R->R:=[r1,r2:R](Rplus r1 (Ropp r2)).

(*********************************************************)
(*       Field axioms                                   *)
(*********************************************************)
(*********************************************************)
(*       Addition                                        *)
(*********************************************************)

(**********)
Axiom Rplus_sym:(r1,r2:R)((Rplus r1 r2)==(Rplus r2 r1)).

(**********)
Axiom Rplus_assoc:(r1,r2,r3:R)
  ((Rplus (Rplus r1 r2) r3)==(Rplus r1 (Rplus r2 r3))).

(**********)
Axiom Rplus_Ropp_r:(r:R)((Rplus r (Ropp r))==R0).
Hints Resolve Rplus_Ropp_r : real v62.

(**********)
Axiom Rplus_ne:(r:R)(((Rplus r R0)==r)/\((Rplus R0 r)==r)).
Hints Resolve Rplus_ne : real v62.

(***********************************************************)       
(*        Multiplication                                   *)
(***********************************************************)

(**********)
Axiom Rmult_sym:(r1,r2:R)((Rmult r1 r2)==(Rmult r2 r1)).
Hints Resolve Rmult_sym : real v62. 

(**********)
Axiom Rmult_assoc:(r1,r2,r3:R)
  ((Rmult (Rmult r1 r2) r3)==(Rmult r1 (Rmult r2 r3))).
Hints Resolve Rmult_assoc : real v62.

(**********)
Axiom Rinv_l:(r:R)(~(r==R0))->((Rmult (Rinv r) r)==R1).

(**********)
Axiom Rmult_ne:(r:R)(((Rmult r R1)==r)/\((Rmult R1 r)==r)).
Hints Resolve Rmult_ne : real v62.

(**********)
Axiom R1_neq_R0:(~R1==R0).

(*********************************************************)
(*       Distributivity                                  *)
(*********************************************************)

(**********)
Axiom Rmult_Rplus_distr:(r1,r2,r3:R)
  ((Rmult r1 (Rplus r2 r3))==(Rplus (Rmult r1 r2) (Rmult r1 r3))).
Hints Resolve Rmult_Rplus_distr : real v62.

(*********************************************************)
(*       Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(*       Total Order                                     *)
(*********************************************************)

(**********)
Axiom total_order_T:(r1,r2:R)(sumorT (sumboolT (Rlt r1 r2) (r1==r2)) 
                                   (Rgt r1 r2)).

(*********************************************************)
(*       Lower                                           *)
(*********************************************************)

(**********)
Axiom Rlt_antisym:(r1,r2:R)(Rlt r1 r2) -> ~(Rlt r2 r1).

(**********)
Axiom Rlt_trans:(r1,r2,r3:R)
  (Rlt r1 r2)->(Rlt r2 r3)->(Rlt r1 r3).

(**********)
Axiom Rlt_compatibility:(r,r1,r2:R)(Rlt r1 r2)->
      (Rlt (Rplus r r1) (Rplus r r2)).

(**********)
Axiom Rlt_monotony:(r,r1,r2:R)(Rlt R0 r)->(Rlt r1 r2)->
      (Rlt (Rmult r r1) (Rmult r r2)).

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
Axiom archimed:(r:R)(Rgt (IZR (up r)) r)/\
                    (Rle (Rminus (IZR (up r)) r) R1).

(**********************************************************)
(*       R Complete                                        *)
(**********************************************************)

(**********)
Definition is_upper_bound:=[E:R->Prop][m:R](x:R)(E x)->(Rle x m).

(**********)
Definition bound:=[E:R->Prop](ExT [m:R](is_upper_bound E m)).

(**********)
Definition is_lub:=[E:R->Prop][m:R]
    (is_upper_bound E m)/\(b:R)(is_upper_bound E b)->(Rle m b).

(**********)
Axiom complet:(E:R->Prop)(bound E)->
              (ExT [x:R] (E x))->
              (ExT [m:R](is_lub E m)).

