(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Util
open Formula
open Tacmach
open Names

let priority=function (* pure heuristics, <=0 for non reversible *)
      Lfalse             ->1000
    | Land _             ->  90
    | Lor _              ->  40
    | Lforall (_,_)      -> -20
    | Lexists            ->  60
    | LAatom _           ->   0
    | LAfalse            -> 100
    | LAand (_,_)      ->  80
    | LAor (_,_)       ->  70
    | LAforall _         -> -30
    | LAexists (_,_,_,_) ->  50
    | LAarrow  (_,_,_)   ->   -10 


let right_atomic=function
    Atomic _->true
  | Complex (_,_) ->false
      
let right_reversible=
  function
      Rarrow | Rand | Rforall->true
    | _ ->false
	
let left_reversible lpat=(priority lpat)>0

module OrderedFormula=
struct
  type t=left_formula
  let compare e1 e2=(priority e1.pat) - (priority e2.pat)
end

module OrderedConstr=
struct
  type t=constr
  let compare=Pervasives.compare
end

module CM=Map.Make(OrderedConstr)

module HP=Heap.Functional(OrderedFormula)

type t=
    {hyps:HP.t;hatoms:identifier CM.t;gl:right_formula}

let add_left (nam,t) seq metagen=
  match build_left_entry nam t metagen with
      Left f->{seq with hyps=HP.add f seq.hyps}
    | Right t->{seq with hatoms=CM.add t nam seq.hatoms}

let re_add_left_list lf seq=
  {seq with hyps=List.fold_right HP.add lf seq.hyps} 

let change_right t seq metagen=
  {seq with gl=build_right_entry t metagen}

let find_left t seq=CM.find t seq.hatoms

let atomic_right seq= right_atomic seq.gl 

let rev_left seq=
  try
    let lpat=(HP.maximum seq.hyps).pat in
      left_reversible lpat
  with Heap.EmptyHeap -> false

let is_empty_left seq=
  seq.hyps=HP.empty

let take_left seq=
  let hd=HP.maximum seq.hyps
  and hp=HP.remove seq.hyps in
    hd,{seq with hyps=hp}

let take_right seq=seq.gl

let empty_seq=
  {hyps=HP.empty;
   hatoms=CM.empty;
   gl=Atomic (mkMeta 1)}

