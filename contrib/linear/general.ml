(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ *)

let substract l1 l2= 
  let rec sub_aux=function
      []->[]
    | x::q->if List.mem x l2 then sub_aux q else x::(sub_aux q)
  in sub_aux l1	

let rec union l1=function
    []->l1
  | x::q-> if List.mem x l1 then union l1 q else x::(union l1 q)
  
(*** glue : make the concatenation of the lists of a lists list *****)

let rec glue = function
    (l::ll) -> union l (glue ll)
  | [] -> []

(*** disjoint l1 l2 : returns true if the lists l1 and l2 are disjoint ******)

let disjoint l1 l2 = 
  let rec disjoint_rec = function
      (a::ll1) -> if List.mem a l2 then false else disjoint_rec ll1
    | [] -> true
  in disjoint_rec l1

(*** such_that : 'a list -> ('a -> bool) -> 'a list *******)

let such_that l p = 
  let rec such_rec = function
      a::ll -> if (p a) then a::(such_rec ll) else such_rec ll
    | [] -> []
  in such_rec l
