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
open Libnames
open Pp

let newcnt ()=
  let cnt=ref (-1) in
    fun b->if b then incr cnt;!cnt

let priority = function (* pure heuristics, <=0 for non reversible *)
      Lfalse             ->1000
    | Land _             ->  90
    | Lor _              ->  40
    | Lforall (_,_)      -> -30
    | Lexists            ->  60
    | Levaluable _       -> 100
    | LA(_,lap) ->
	match lap with
	    LLatom             ->   0
	  | LLfalse            -> 100
	  | LLand (_,_)        ->  80
	  | LLor (_,_)         ->  70
	  | LLforall _         -> -20
	  | LLexists (_,_,_,_) ->  50
	  | LLarrow  (_,_,_)   -> -10 
	  | LLevaluable _      -> 100

let right_reversible=
  function
      Rarrow | Rand | Rforall | Revaluable _ ->true
    | _ ->false
	
let left_reversible lpat=(priority lpat)>0

module OrderedFormula=
struct
  type t=left_formula
  let compare e1 e2=
	(priority e1.pat) - (priority e2.pat)
end

module OrderedConstr=
struct
  type t=constr
  let rec compare c1 c2=
    match (kind_of_term c1,kind_of_term c2) with
	(Prod(_,a1,b1),Prod(_,a2,b2))
      | (Lambda(_,a1,b1),Lambda(_,a2,b2)) ->
	  (compare a1 a2) +- (compare b1 b2)
      | (LetIn(_,a1,b1,aa1),LetIn(_,a2,b2,aa2)) ->
 	  ((compare a1 a2) +- (compare b1 b2)) +- (compare aa1 aa2)
      | _-> Pervasives.compare c1 c2
end

module Hitem=
struct 
  type t=(global_reference * constr option)
  let compare (id1,co1) (id2,co2)=
    (Pervasives.compare id1 id2) +- 
    (match co1,co2 with
	 Some c1,Some c2 -> OrderedConstr.compare c1 c2
       | _->Pervasives.compare co1 co2)
end

module CM=Map.Make(OrderedConstr)

module History=Set.Make(Hitem)

let cm_add typ nam cm=
  try 
    let l=CM.find typ cm in CM.add typ (nam::l) cm
  with
      Not_found->CM.add typ [nam] cm
	
let cm_remove typ nam cm=
  try
    let l=CM.find typ cm in 
    let l0=List.filter (fun id->id<>nam) l in
      match l0 with 
	  []->CM.remove typ cm
	| _ ->CM.add typ l0 cm
      with Not_found ->cm

module HP=Heap.Functional(OrderedFormula)

type t=
    {redexes:HP.t;
     context:(global_reference list) CM.t;
     latoms:constr list;
     gl:right_formula;
     cnt:counter;
     history:History.t;
     depth:int}

let deepen seq={seq with depth=seq.depth-1}
 
let record id topt seq={seq with history=History.add (id,topt) seq.history}

let lookup id topt seq=History.mem (id,topt) seq.history

let add_left (nam,t) seq internal gl=
  match build_left_entry nam t internal gl seq.cnt with
      Left f->{seq with 
		 redexes=HP.add f seq.redexes;
		 context=cm_add f.constr nam seq.context}
    | Right t->{seq with 
		  context=cm_add t nam seq.context;
		  latoms=t::seq.latoms}

let re_add_left_list lf seq=
  {seq with 
     redexes=List.fold_right HP.add lf seq.redexes;
     context=List.fold_right 
	       (fun f cm->cm_add f.constr f.id cm) lf seq.context}

let change_right t seq gl=
  {seq with gl=build_right_entry t gl seq.cnt}

let find_left t seq=List.hd (CM.find t seq.context)

let rev_left seq=
  try
    let lpat=(HP.maximum seq.redexes).pat in
      left_reversible lpat
  with Heap.EmptyHeap -> false

let is_empty_left seq=
  seq.redexes=HP.empty

let take_left seq=
  let hd=HP.maximum seq.redexes
  and hp=HP.remove seq.redexes in
    hd,{seq with 
	  redexes=hp;
	  context=cm_remove hd.constr hd.id seq.context}

let take_right seq=seq.gl

let empty_seq depth=
  {redexes=HP.empty;   
   context=CM.empty;
   latoms=[];
   gl=Atomic (mkMeta 1);
   cnt=newcnt ();
   history=History.empty;
   depth=depth}

let create_with_ref_list l depth gl=
  let f gr seq=
    let c=constr_of_reference gr in    
    let typ=(pf_type_of gl c) in
      add_left (gr,typ) seq false gl in
    List.fold_right f l (empty_seq depth)

open Auto

let create_with_auto_hints depth gl=
  let seqref=ref (empty_seq depth) in
  let f p_a_t =
    match p_a_t.code with
	Res_pf (c,_) | Give_exact c
      | Res_pf_THEN_trivial_fail (c,_) ->
	  (try 
	     let gr=reference_of_constr c in 
	     let typ=(pf_type_of gl c) in
	       seqref:=add_left (gr,typ) !seqref false gl
	   with Not_found->())
      | _-> () in
  let g _ l=List.iter f l in
  let h str hdb=Hint_db.iter g hdb in
    Util.Stringmap.iter h (!searchtable);
    !seqref

let print_cmap map=
  
  let print_entry c l s=
    let xc=Constrextern.extern_constr false (Global.env ()) c in
      str "| " ++ 
      Util.prlist (Ppconstr.pr_global Idset.empty) l ++ 
      str " : " ++
      Ppconstr.pr_constr xc ++ 
      cut () ++ 
      s in
    msgnl (v 0 
	     (str "-----" ++ 
	      cut () ++
	      CM.fold print_entry map (mt ()) ++
	      str "-----"))

	
