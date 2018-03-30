(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Cring.
Require Export Integral_domain.
Require Export Ncring_initial.
Require Export Omega.

Instance Zcri: (Cring (Rr:=Zr)).
red. exact Z.mul_comm. Defined.

Lemma Z_one_zero: 1%Z <> 0%Z.
omega. 
Qed.

Instance Zdi : (Integral_domain (Rcr:=Zcri)). 
constructor. 
exact Zmult_integral. exact Z_one_zero. Defined.
