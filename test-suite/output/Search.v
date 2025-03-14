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

Search "_assoc".
Search "+".
Search hyp:bool -headhyp:bool.
Search concl:bool -headconcl:bool.
Search [ is:Definition headconcl:nat | is:Lemma (_ + _) ].

(* used to print something between search outputs, otherwise we can't
   tell which lines are from which command *)
Require Import Ltac2.Printf.

Module BlacklistLocals.
  Axiom T : Type.
  Axiom t : T.
  Local Definition t_alias := t.

  Ltac2 Eval printf "should say both t and t_alias".
  Search T.
End BlacklistLocals.

Ltac2 Eval printf "should say only t".
Search BlacklistLocals.T.

Unset Search Blacklist Locals.
Ltac2 Eval printf "should say both t and t_alias".
Search BlacklistLocals.T.
