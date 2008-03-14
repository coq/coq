(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rstar.

Section Newman.

Variable A : Type. 
Variable R : A -> A -> Prop.

Let Rstar := Rstar A R. 
Let Rstar_reflexive := Rstar_reflexive A R.
Let Rstar_transitive := Rstar_transitive A R.
Let Rstar_Rstar' := Rstar_Rstar' A R.

Definition coherence (x y:A) := ex2 (Rstar x) (Rstar y).

Theorem coherence_intro :
  forall x y z:A, Rstar x z -> Rstar y z -> coherence x y.
Proof fun (x y z:A) (h1:Rstar x z) (h2:Rstar y z) =>
  ex_intro2 (Rstar x) (Rstar y) z h1 h2.
  
(** A very simple case of coherence : *)

Lemma Rstar_coherence : forall x y:A, Rstar x y -> coherence x y.
Proof
  fun (x y:A) (h:Rstar x y) => coherence_intro x y y h (Rstar_reflexive y).  
  
(** coherence is symmetric *)
Lemma coherence_sym : forall x y:A, coherence x y -> coherence y x.
Proof
  fun (x y:A) (h:coherence x y) =>
    ex2_ind
      (fun (w:A) (h1:Rstar x w) (h2:Rstar y w) =>
        coherence_intro y x w h2 h1) h.

Definition confluence (x:A) :=
  forall y z:A, Rstar x y -> Rstar x z -> coherence y z.  
  
Definition local_confluence (x:A) :=
  forall y z:A, R x y -> R x z -> coherence y z.  
  
Definition noetherian :=
  forall (x:A) (P:A -> Prop),
    (forall y:A, (forall z:A, R y z -> P z) -> P y) -> P x.  
  
Section Newman_section.

  (** The general hypotheses of the theorem *)

  Hypothesis Hyp1 : noetherian.
  Hypothesis Hyp2 : forall x:A, local_confluence x.  
  
  (** The induction hypothesis *)

  Section Induct.
    Variable x : A.
    Hypothesis hyp_ind : forall u:A, R x u -> confluence u.  
  
    (** Confluence in [x] *)

    Variables y z : A.  
    Hypothesis h1 : Rstar x y.  
    Hypothesis h2 : Rstar x z.  
  
    (** particular case [x->u] and [u->*y]   *)
    Section Newman_.
      Variable u : A.  
      Hypothesis t1 : R x u.  
      Hypothesis t2 : Rstar u y.  
      
      (** In the usual diagram, we assume also [x->v] and [v->*z] *)
      
      Theorem Diagram : forall (v:A) (u1:R x v) (u2:Rstar v z), coherence y z.
      Proof
       (* We draw the diagram ! *)
      fun (v:A) (u1:R x v) (u2:Rstar v z) =>
	ex2_ind
	 (* local confluence in x for u,v *)
	 (* gives w, u->*w and v->*w *)
	(fun (w:A) (s1:Rstar u w) (s2:Rstar v w) =>
          ex2_ind
              (* confluence in u => coherence(y,w) *)
              (* gives a, y->*a and z->*a *)
          (fun (a:A) (v1:Rstar y a) (v2:Rstar w a) =>
            ex2_ind
              (* confluence in v => coherence(a,z) *)
              (* gives b, a->*b and z->*b *)
            (fun (b:A) (w1:Rstar a b) (w2:Rstar z b) =>
              coherence_intro y z b (Rstar_transitive y a b v1 w1) w2)
            (hyp_ind v u1 a z (Rstar_transitive v w a s2 v2) u2))
          (hyp_ind u t1 y w t2 s1)) (Hyp2 x u v t1 u1).
  
      Theorem caseRxy : coherence y z.
      Proof
        Rstar_Rstar' x z h2 (fun v w:A => coherence y w)
	(coherence_sym x y (Rstar_coherence x y h1)) (*i case x=z i*)
	Diagram.                                     (*i case x->v->*z i*)
    End Newman_.

    Theorem Ind_proof : coherence y z.
    Proof
      Rstar_Rstar' x y h1 (fun u v:A => coherence v z)
      (Rstar_coherence x z h2) (*i case x=y i*)
      caseRxy.                                   (*i case x->u->*z i*)
  End Induct.

  Theorem Newman : forall x:A, confluence x.
  Proof fun x:A => Hyp1 x confluence Ind_proof.  

End Newman_section.


End Newman.
