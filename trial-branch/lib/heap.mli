(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Heaps *)

module type Ordered = sig
  type t
  val compare : t -> t -> int
end

module type S =sig
  
  (* Type of functional heaps *)
  type t

  (* Type of elements *)
  type elt
    
  (* The empty heap *)
  val empty : t
    
  (* [add x h] returns a new heap containing the elements of [h], plus [x];
     complexity $O(log(n))$ *)
  val add : elt -> t -> t
    
  (* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> elt
    
  (* [remove h] returns a new heap containing the elements of [h], except
     the maximum of [h]; raises [EmptyHeap] when [h] is empty; 
     complexity $O(log(n))$ *) 
  val remove : t -> t
    
  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit
    
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    
end

exception EmptyHeap

(*S Functional implementation. *)

module Functional(X: Ordered) : S with type elt=X.t
