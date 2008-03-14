(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Tuples *)

Definition tuple_1 (X:Set) := X.
Definition tuple_2 := prod.
Definition Build_tuple_2 := pair.
Definition proj_2_1 := fst.
Definition proj_2_2 := snd.

Record tuple_3 (T1 T2 T3:Set) : Set := 
  {proj_3_1 : T1; proj_3_2 : T2; proj_3_3 : T3}.

Record tuple_4 (T1 T2 T3 T4:Set) : Set := 
  {proj_4_1 : T1; proj_4_2 : T2; proj_4_3 : T3; proj_4_4 : T4}.

Record tuple_5 (T1 T2 T3 T4 T5:Set) : Set := 
  {proj_5_1 : T1; proj_5_2 : T2; proj_5_3 : T3; proj_5_4 : T4; proj_5_5 : T5}.

Record tuple_6 (T1 T2 T3 T4 T5 T6:Set) : Set := 
  {proj_6_1 : T1;
   proj_6_2 : T2;
   proj_6_3 : T3;
   proj_6_4 : T4;
   proj_6_5 : T5;
   proj_6_6 : T6}.

Record tuple_7 (T1 T2 T3 T4 T5 T6 T7:Set) : Set := 
  {proj_7_1 : T1;
   proj_7_2 : T2;
   proj_7_3 : T3;
   proj_7_4 : T4;
   proj_7_5 : T5;
   proj_7_6 : T6;
   proj_7_7 : T7}.


(* Existentials *)

Definition sig_1 := sig.
Definition exist_1 := exist.

Inductive sig_2 (T1 T2:Set) (P:T1 -> T2 -> Prop) : Set :=
    exist_2 : forall (x1:T1) (x2:T2), P x1 x2 -> sig_2 T1 T2 P.

Inductive sig_3 (T1 T2 T3:Set) (P:T1 -> T2 -> T3 -> Prop) : Set :=
    exist_3 : forall (x1:T1) (x2:T2) (x3:T3), P x1 x2 x3 -> sig_3 T1 T2 T3 P.


Inductive sig_4 (T1 T2 T3 T4:Set) (P:T1 -> T2 -> T3 -> T4 -> Prop) : Set :=
    exist_4 :
      forall (x1:T1) (x2:T2) (x3:T3) (x4:T4),
        P x1 x2 x3 x4 -> sig_4 T1 T2 T3 T4 P.

Inductive sig_5 (T1 T2 T3 T4 T5:Set) (P:T1 -> T2 -> T3 -> T4 -> T5 -> Prop) :
Set :=
    exist_5 :
      forall (x1:T1) (x2:T2) (x3:T3) (x4:T4) (x5:T5),
        P x1 x2 x3 x4 x5 -> sig_5 T1 T2 T3 T4 T5 P.

Inductive sig_6 (T1 T2 T3 T4 T5 T6:Set)
(P:T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> Prop) : Set :=
    exist_6 :
      forall (x1:T1) (x2:T2) (x3:T3) (x4:T4) (x5:T5) 
        (x6:T6), P x1 x2 x3 x4 x5 x6 -> sig_6 T1 T2 T3 T4 T5 T6 P.

Inductive sig_7 (T1 T2 T3 T4 T5 T6 T7:Set)
(P:T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> Prop) : Set :=
    exist_7 :
      forall (x1:T1) (x2:T2) (x3:T3) (x4:T4) (x5:T5) 
        (x6:T6) (x7:T7),
        P x1 x2 x3 x4 x5 x6 x7 -> sig_7 T1 T2 T3 T4 T5 T6 T7 P.

Inductive sig_8 (T1 T2 T3 T4 T5 T6 T7 T8:Set)
(P:T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> Prop) : Set :=
    exist_8 :
      forall (x1:T1) (x2:T2) (x3:T3) (x4:T4) (x5:T5) 
        (x6:T6) (x7:T7) (x8:T8),
        P x1 x2 x3 x4 x5 x6 x7 x8 -> sig_8 T1 T2 T3 T4 T5 T6 T7 T8 P.      

Inductive dep_tuple_2 (T1 T2:Set) (P:T1 -> T2 -> Set) : Set :=
    Build_dep_tuple_2 :
      forall (x1:T1) (x2:T2), P x1 x2 -> dep_tuple_2 T1 T2 P.

Inductive dep_tuple_3 (T1 T2 T3:Set) (P:T1 -> T2 -> T3 -> Set) : Set :=
    Build_dep_tuple_3 :
      forall (x1:T1) (x2:T2) (x3:T3), P x1 x2 x3 -> dep_tuple_3 T1 T2 T3 P.

