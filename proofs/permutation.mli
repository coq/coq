(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: permutation.mli aspiwack $ *)

(* This module implements the permutations of arrays (it can probably
   be extended to lists). *)

(* This is not a module which is specific to the proof system, but it
   is currently used only by it, thus it is held in the directory
   proofs/. *)

type permutation

(* Function to build a permutation from an array. 
   Raises Invalid_arg "Permutation.of_array: ill formed permutation"
   if the array is not a permutation of [| 0 1 ... (n-1) |] *)
val of_array : int array -> permutation

(* Function to permute an array.
   Raises Invalid_argument "Permutation.permute: array and permutation size do not match"
   if the size of the array is smaller than that of the permutation.
   If the size of the array is bigger than the permutation, then the permutation   is extended *)
val permute : permutation -> 'a array -> 'a array
