(* This requires cumulativity *)

Definition Type2 := Type.
Definition Type1 := Type : Type2.

Lemma lem1 : (True->Type1)->Type2.
Intro H.
Apply H.
Exact I.
Qed.

Lemma lem2 : (A:Type)(P:A->Type)(x:A)((y:A)(x==y)->(P y))->(P x).
Auto.
Qed.

Lemma lem3 : (P:Prop)P.
Intro P ; Pattern P.
Apply lem2.
Abort.

(* Check managing of universe constraints in inversion *)
(* Bug report #855 *)

Inductive dep_eq : (X:Type) X -> X -> Prop :=
   | intro_eq : (X:Type) (f:X)(dep_eq X f f)
   | intro_feq : (A:Type) (B:A->Type)
                 let T = (x:A)(B x) in
                 (f, g:T) (x:A)
                 (dep_eq (B x) (f x) (g x)) ->
                 (dep_eq T f g).
                                                                                
Require Import Relations.
                                                                                
Theorem dep_eq_trans : (X:Type) (transitive X (dep_eq X)).
Proof.
  Unfold transitive.
  Intros X f g h H1 H2.
  Inversion H1.
Abort.


(* Submitted by Bas Spitters (bug report #935) *)

(* This is a problem with the status of the type in LetIn: is it a
   user-provided one or an inferred one? At the current time, the
   kernel type-check the type in LetIn, which means that it must be
   considered as user-provided when calling the kernel. However, in
   practice it is inferred so that a universe refresh is needed to set
   its status as "user-provided".

   Especially, universe refreshing was not done for "set/pose" *)

Lemma ind_unsec:(Q:nat->Type)True. 
Intro.
Pose C:= (m:?)(Q m)->(Q m).
Exact I.
Qed.
