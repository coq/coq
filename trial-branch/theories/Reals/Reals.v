(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** The library REALS is divided in 6 parts :
   - Rbase: basic lemmas on R
            equalities and inequalities
            Ring and Field are instantiated on R
   - Rfunctions: some useful functions (Rabsolu, Rmin, Rmax, fact...)
   - SeqSeries: theory of sequences and series
   - Rtrigo: theory of trigonometric functions
   - Ranalysis: some topology and general results of real analysis (mean value theorem, intermediate value theorem,...)
   - Integration: Newton and Riemann' integrals

  Tactics are:
  - DiscrR: for goals like ``?1<>0``
  - Sup: for goals like ``?1<?2``
  - RCompute: for equalities with constants like ``10*10==100``
  - Reg: for goals like (continuity_pt ?1 ?2) or (derivable_pt ?1 ?2) *)
  
Require Export Rbase.
Require Export Rfunctions.
Require Export SeqSeries.
Require Export Rtrigo.
Require Export Ranalysis.
Require Export Integration.