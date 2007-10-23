(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: biassoc.ml aspiwack $ *)

(* This modules implements a bidirectional association table,
   that is a table where both values can be seen as the key for
   the association.
   For soundness reason, when adding an association [(a,b)] both
   [a] and [b] must be unique.

   Map is a reasonably efficient datastructure, which compares rather
   well (in average) to the more imperative Hashtables. In that respect
   and since persistent datastructures are used in the kernel, I write
   this in the functional style.

   This module have been originally written for being used both in the
   retroknowledge for its internal representation (thus in the kernel)
   and in the interactive proof system for associating dependent goals
   to an evar. *)

(* The internal representation is a straightforward pair of Maps
   (one from a type 'a to a type 'b, and the other from the 
   type 'b to the type 'a). Both are updated synchronously to 
   provide fast access in both directions. *)




type ('a,'b) biassoc = { left:('a,'b) Gmap.t ; right:('b,'a) Gmap.t }
    
let empty = { left=Gmap.empty ; right=Gmap.empty }
let is_empty bm = (Gmap.is_empty bm.left)&&(Gmap.is_empty bm.right)
  
let find_with_left lt bm = Gmap.find lt bm.left
let find_with_right rt bm = Gmap.find rt bm.right
  
let mem_with_left lt bm = Gmap.mem lt bm.left
let mem_with_right rt bm = Gmap.mem rt bm.right
  
(* remove functions are not a direct lifting of the 
   functions from either components, since you have to 
   remove the corresponding binding in the second Map *)
let remove_with_left lt bm = 
  try 
    let rt = find_with_left lt bm in
      { left = Gmap.remove lt bm.left ;
        right = Gmap.remove rt bm.right }
  with Not_found ->
    (* if there is no (lt, ?) in the left Map, then there
       is no (?,lt) in the Right table. Thus bm is already
       free of any reference to lt *)
    bm
      
let remove_with_right rt bm = (* see remove_with_left *)
  try 
    let lt = find_with_right rt bm in
      { left = Gmap.remove lt bm.left ;
        right = Gmap.remove rt bm.right }
  with Not_found ->
    bm
      
let add lt rt bm = 
  if not (mem_with_left lt bm) && not (mem_with_right rt bm) then
    { left = Gmap.add lt rt bm.left ;
      right = Gmap.add rt lt bm.right }
  else
    raise (Invalid_argument "Biassoc: non unique values")

