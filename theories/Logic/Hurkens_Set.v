(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                            Projet LogiCal                                *)
(*                                                                          *)
(*                     INRIA                        LRI-CNRS                *)
(*              Rocquencourt                        Orsay                   *)
(*                                                                          *)
(*                              May 29th 2002                               *)
(*                                                                          *)
(****************************************************************************)
(*                            Hurkens_set.v                                 *)
(****************************************************************************)

(*i logic: "-strongly-constructive" i*)

(** This is Hurkens paradox [Hurkens] in system U-, adapted by Herman
    Geuvers [Geuvers] to show the inconsistency in the pure calculus of
    constructions of a retract from Prop into a small type. This file
    focus on the case of a retract into a small type in impredicative
    Set. As a consequence, Excluded Middle in Set is inconsistent with
    the impredicativity of Set.


    References:

    - [Hurkens] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [Geuvers] "Inconsistency of Classical Logic in Type Theory", 2001
      (see www.cs.kun.nl/~herman/note.ps.gz).
*)

(** We show that Hurkens paradox still hold for a retract from the
    negative fragment of Prop only, into bool:Set *)

Section Hurkens_set_neg.

Variable p2b : Prop -> bool.
Variable b2p : bool -> Prop.
Definition dn [A:Prop] := (A->False)->False.
Hypothesis p2p1 : (A:Prop)(dn (b2p (p2b A)))->(dn A).
Hypothesis p2p2 : (A:Prop)A->(b2p (p2b A)).

Definition V := (A:Set)((A->bool)->(A->bool))->(A->bool).
Definition U := V->bool.
Definition sb : V -> V := [z][A;r;a](r (z A r) a).
Definition le : (U->bool)->(U->bool) := [i][x](x [A;r;a](i [v](sb v A r a))).
Definition induct: (U->bool)->Prop := [i](x:U)(b2p (le i x))->(dn (b2p (i x))).
Definition WF : U := [z](p2b (induct (z U le))).
Definition I : U->Prop :=
  [x]((i:U->bool)(b2p (le i x))->(dn (b2p (i [v](sb v U le x)))))->False.

Lemma Omega : (i:U->bool)(induct i)->(dn (b2p (i WF))).
Intros i y.
Apply y.
Unfold le WF induct.
Apply p2p2.
Intros x H0.
Apply y.
Exact H0.
Qed.

Lemma lemma : (induct [u](p2b (I u))).
Unfold induct.
Intros x p.
Intro H; Apply H.
Apply (p2p2 (I x)).
Intro q.
Apply (p2p1 (I [v:V](sb v U le x)) (q [u](p2b (I u)) p)).
Intro H'; Apply H'.
Intro i.
Apply q with i:=[y:?](i [v:V](sb v U le y)).
Qed.

Lemma lemma2 : ((i:U->bool)(induct i)->(dn (b2p (i WF))))->False.
Intro x.
Apply (p2p1 (I WF) (x [u](p2b (I u)) lemma)).
Intro H; Apply H.
Intros i H0.
Apply (x [y](i [v](sb v U le y))).
Assert H1 : (dn (induct [y:U](i [v:V](sb v U le y)))).
Assert H0' : (dn (b2p (le i WF))).
  Intro H1; Apply H1; Exact H0.
Apply (p2p1 ? H0').
Intros y H2 H3.
Apply H1.
Intro H4.
Unfold induct in H4.
Unfold dn in H4.
Apply (H4 y H2 H3).
Qed.

Theorem Hurkens_set_neg : False.
Exact (lemma2 Omega).
Qed.

End Hurkens_set_neg.

Section EM_set_neg_inconsistency.

Variable EM_set_neg : (A:Prop){~A}+{~~A}.

Definition p2b [A:Prop] := if (EM_set_neg A) then [_]false else [_]true.
Definition b2p [b:bool] := b=true.

Lemma p2p1 : (A:Prop)~~(b2p (p2b A))->~~A.
Proof.
Intro A.
Unfold p2b.
NewDestruct (EM_set_neg A) as [_|Ha].
  Unfold b2p; Intros H Hna; Apply H; Discriminate.
  Tauto.
Qed.

Lemma p2p2 : (A:Prop)A->(b2p (p2b A)).
Proof.
Intro A.
Unfold p2b.
NewDestruct (EM_set_neg A) as [Hna|_].
  Intro Ha; Elim (Hna Ha).
  Intro; Unfold b2p; Reflexivity.
Qed.

Theorem not_EM_set_neg : False.
Proof.
Apply Hurkens_set_neg with p2b b2p.
Apply p2p1.
Apply p2p2.
Qed.

End EM_set_neg_inconsistency.

Section EM_set_inconsistency.

Variable EM_set_neg : (A:Prop){A}+{~A}.

Theorem not_EM_set : False.
Proof.
Apply not_EM_set_neg.
Intro A; Apply EM_set_neg.
Qed.

End EM_set_inconsistency.

