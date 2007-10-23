(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: permutation.ml aspiwack $ *)

(* This module implements the permutations of arrays (it can probably
   be extended to lists). *)

(* This is not a module which is specific to the proof system, but it
   is currently used only by it, thus it is held in the directory
   proofs/. *)

type permutation = int array

(* Function checking if an array is of the form [| 0 1 ... (n-1) |] *)
let check_correct =
  let locally_correct ix elt =
    if ix = elt then
      ()
    else
      raise Not_found
  in
  fun arr ->
    try
      Array.iteri locally_correct arr ;
      true
    with Not_found ->
      false
 

(* Function checking if an array is a permutation of [| 0 1 ... (n-1) |] *)
let check_permutation arr =
  let new_arr = Array.copy arr in
  Array.fast_sort compare new_arr;
  check_correct new_arr

(* Function to build a permutation from an array. 
   Raises Invalid_argument "Permutation.of_array: ill formed permutation"
   if the array is not a permutation of [| 0 1 ... (n-1) |] *)
let of_array arr =
  if check_permutation arr then
    Array.copy arr
  else
    invalid_arg "Permutation.of_array: ill formed permutation"

(* Produces an occurence of the identity of size n *)
let identity n =
  Array.init n (fun i -> i)

(* For an [n > Array.length perm], it extends the permutation with the
   identity *)
let extend perm n =
  let ext = identity n in
  Array.blit perm 0 ext 0 (Array.length perm);
  ext

(* Function to permute an array.
   Raises Invalid_argument "Permutation.permute: array and permutation size do not match"
   if the size of the array is smaller than that of the permutation.
   If the size of the array is bigger than the permutation, then the permutation   is extended *)
let permute =
  (* permutes [arr] according to [per] both must be of length [len] *)
  let unsafe_permute perm arr len =
    Array.init len (fun i-> arr.(perm.(i)))
  in
  fun perm arr ->
    let plen = Array.length perm in
    let alen = Array.length arr in
    if alen > plen then
      unsafe_permute (extend perm alen) arr alen
    else if alen = plen then
      unsafe_permute perm arr alen
    else
      invalid_arg "Permutation.permute: array and permutation size do not match"
