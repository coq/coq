(* Some tests of the Search command *)

Search le.				(* app nodes *)
Search bool. 				(* no apps *)
Search (@eq nat).			(* complex pattern *)
Search (@eq _ _ true).
Search (@eq _ _ _) true -false.         (* andb_prop *)
Search (@eq _ _ _) true -false "prop" -"intro".  (* andb_prop *)

Definition newdef := fun x:nat => x.

Goal forall n:nat, n <> newdef n -> newdef n <> n -> False.
  cut False.
  intros _ n h h'.
  Search n.                             (* search hypothesis *)
  Search newdef.                        (* search hypothesis *)
  Search ( _ <> newdef _).              (* search hypothesis, pattern *)
  Search ( _ <> newdef _) -"h'".        (* search hypothesis, pattern *)

  1:Search newdef.
  2:Search newdef.

  Fail 3:Search newdef.
  Fail 1-2:Search newdef.
  Fail all:Search newdef.
Abort.

Goal forall n (P:nat -> Prop), P n -> ~P n -> False.
  intros n P h h'.
  Search P.                 (* search hypothesis also for patterns *)
  Search (P _).             (* search hypothesis also for patterns *)
  Search (P n).             (* search hypothesis also for patterns *)
  Search (P _) -"h'".       (* search hypothesis also for patterns *)
  Search (P _) -not.       (* search hypothesis also for patterns *)

Abort.

Module M.
Section S.
Variable A:Type.
Variable a:A.
Theorem Thm (b:A) : True.
Search A. (* Test search in hypotheses *)
Abort.
End S.
End M.

(* Reproduce the example of the doc *)

Reset Initial.

Search "_assoc".
Search "+".
Search hyp:bool -headhyp:bool.
Search concl:bool -headconcl:bool.
Search [ is:Definition headconcl:nat | is:Lemma (_ + _) ].

Require Import PeanoNat.

Search (_ ?n ?m = _ ?m ?n).
Search "'mod'" -"mod".
Search "mod"%nat -"mod".

Reset Initial.

Require Import Morphisms.

Search is:Instance [ Reflexive | Symmetric ].

Module Bug12525.
  (* This was revealing a kernel bug with delta-resolution *)
  Module A. Axiom a:Prop. Axiom b:a. End A.
  Module B. Include A. End B.
  Module M.
    Search B.a.
  End M.
End Bug12525.

From Coq Require Lia.

Module Bug12647.
  (* Similar to #12525 *)
  Module Type Foo.
  Axiom P : nat -> Prop.
  Axiom L : P 0.
  End Foo.

  Module Bar (F : Foo).
  Search F.P.
  End Bar.
End Bug12647.

Module WithCoercions.
  Search headconcl:(_ + _) inside Datatypes.
  Coercion Some_nat := @Some nat.
  Axiom f : None = 0.
  Search (None = 0).
End WithCoercions.

Require Import List.

Module Wish13349.
Search partition "1" inside List.
End Wish13349.

Reset Initial.

Module Bug17963.
Goal exists y, Some y = Some y :> option nat -> True.
eexists. intro H.
Search Some eq.
Abort.
End Bug17963.
