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
(*                                Hurkens.v                                 *)
(****************************************************************************)

(** This is Hurkens paradox [Hurkens] in system U-, adapted by Herman
    Geuvers [Geuvers] to show the inconsistency in the pure calculus of
    constructions of a retract from Prop into a small type.

    References:

    - [Hurkens] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [Geuvers] "Inconsistency of Classical Logic in Type Theory", 2001
      (see www.cs.kun.nl/~herman/note.ps.gz).
*)

Section Paradox.

Variable bool : Prop.
Variable p2b : Prop -> bool.     
Variable b2p : bool -> Prop.
Hypothesis p2p1 : (A:Prop)(b2p (p2b A))->A.
Hypothesis p2p2 : (A:Prop)A->(b2p (p2b A)).
Variable B:Prop.

Definition V := (A:Prop)((A->bool)->(A->bool))->(A->bool).
Definition U := V->bool.
Definition sb : V -> V := [z][A;r;a](r (z A r) a).
Definition le : (U->bool)->(U->bool) := [i][x](x [A;r;a](i [v](sb v A r a))).
Definition induct : (U->bool)->Prop := [i](x:U)(b2p (le i x))->(b2p (i x)).
Definition WF : U := [z](p2b (induct (z U le))).
Definition I : U->Prop :=
  [x]((i:U->bool)(b2p (le i x))->(b2p (i [v](sb v U le x))))->B.

Lemma Omega : (i:U->bool)(induct i)->(b2p (i WF)).
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
Apply (p2p2 (I x)).
Intro q.
Apply (p2p1 (I [v:V](sb v U le x)) (q [u](p2b (I u)) p)).
Intro i.
Apply q with i:=[y:?](i [v:V](sb v U le y)).
Qed.

Lemma lemma2 : ((i:U->bool)(induct i)->(b2p (i WF)))->B.
Intro x.
Apply (p2p1 (I WF) (x [u](p2b (I u)) lemma)).
Intros i H0.
Apply (x [y](i [v](sb v U le y))).
Apply (p2p1 ? H0).
Qed.

Lemma paradox : B.
Exact (lemma2 Omega).
Qed.

End Paradox.
