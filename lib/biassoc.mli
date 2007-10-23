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



type ('a,'b) biassoc
(** the type of bidirectional association table between
    ['a] and ['b] *)
    
val empty : ('a,'b) biassoc
(** the empty bidirectional association table *)
val is_empty : ('a,'b) biassoc -> bool
(** tests the emptyness of a bidirectional association table *)
val add : 'a -> 'b -> ('a,'b) biassoc -> ('a,'b) biassoc
(** [add lt rt bm] return a bidirectional association table identical 
    to [bm] except that there is an additional association between
    [lt] and [rt].
    If [lt] or [rt] are already present in an association in [bm]
    then it raises [Invalid_argument "Biassoc: non unique values"] 
    instead *)
val find_with_left : 'a  -> ('a,'b) biassoc -> 'b
(** [find_with_left lt bm] returns the value associated to [lt] it 
    there is one. It raises [Not_found] otherwise. *)
val find_with_right : 'b -> ('a,'b) biassoc -> 'a
(** [find_with_right] works as [find_with_left] except that
    it implements the other direction of the association. *)
val remove_with_left : 'a -> ('a,'b) biassoc -> ('a,'b) biassoc
(** [remove_with_left lt bm] returns a stack identical to [bm]
    except that any association with [lt] has been removed. *)
val remove_with_right : 'b -> ('a,'b) biassoc -> ('a,'b) biassoc
(** [remove_with_right] works as [remove_with_left] except that
    the key is from the right side of the associations. *)
val mem_with_left : 'a -> ('a,'b) biassoc -> bool
(** [mem_with_left lt bm] returns [true] if there is a value
    associated to [lt] in [bm]. It returns [false] otherwise. *)
val mem_with_right : 'b -> ('a,'b) biassoc -> bool
(** [mem_with_right] works as [mem_with_left] except that it
    implements the other direction. *)
