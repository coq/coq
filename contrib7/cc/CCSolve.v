(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Tactic Definition CCsolve :=
 Repeat (Match Context With
 [ H: ?1 |- ?2] -> 
  Let Heq = FreshId "Heq" In
 (Assert Heq:(?2==?1);[Congruence|(Rewrite Heq;Exact H)])
 |[ H: ?1; G: ?2 -> ?3 |- ?] ->                        
  Let Heq = FreshId "Heq" In
 (Assert Heq:(?2==?1) ;[Congruence|                              
     (Rewrite Heq in G;Generalize (G H);Clear G;Intro G)])).  

