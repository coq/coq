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
    | Lforall (_,_,_)      -> -30 (* must stay at lowest priority *)
    | Lexists _           ->  60
    | Levaluable _       -> 100
    | LA(_,lap) ->
	match lap with
	    LLatom             ->   0
	  | LLfalse            -> 100
	  | LLand (_,_)        ->  80
	  | LLor (_,_)         ->  70
	  | LLforall _         -> -20
	  | LLexists (_,_)     ->  50
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

(* [compare_constr f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's,
   application associativity, binders name and Cases annotations are
   not taken into account *)

let rec compare_list f l1 l2=
  match l1,l2 with
      [],[]-> 0
    | [],_ -> -1
    | _,[] -> 1
    | (h1::q1),(h2::q2) -> (f =? (compare_list f)) h1 h2 q1 q2


let compare_array f v1 v2=  
  let l=Array.length v1 in
  let c=l - Array.length v2 in
    if c=0 then
      let rec comp_aux i=
	if i<0 then 0 
	else
	  let ci=f v1.(i) v2.(i) in
	    if ci=0 then 
	      comp_aux (i-1)
	    else ci
      in comp_aux (l-1)
    else c

let compare_constr_int f t1 t2 =
  match kind_of_term t1, kind_of_term t2 with
    | Rel n1, Rel n2 -> n1 - n2
    | Meta m1, Meta m2 -> m1 - m2
    | Var id1, Var id2 -> Pervasives.compare id1 id2
    | Sort s1, Sort s2 -> Pervasives.compare s1 s2
    | Cast (c1,_), _ -> f c1 t2
    | _, Cast (c2,_) -> f t1 c2
    | Prod (_,t1,c1), Prod (_,t2,c2) 
    | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
	(f =? f) t1 t2 c1 c2 
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> 
	((f =? f) ==? f) b1 b2 t1 t2 c1 c2
    | App (_,_), App (_,_) ->
	let c1,l1=decompose_app t1 
	and c2,l2=decompose_app t2 in
	  (f =? (compare_list f)) c1 c2 l1 l2
    | Evar (e1,l1), Evar (e2,l2) -> 
	((-) =? (compare_array f)) e1 e2 l1 l2
    | Const c1, Const c2 -> Pervasives.compare c1 c2
    | Ind c1, Ind c2 -> Pervasives.compare c1 c2
    | Construct c1, Construct c2 -> Pervasives.compare c1 c2
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
	((f =? f) ==? (compare_array f)) p1 p2 c1 c2 bl1 bl2
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
	((Pervasives.compare =? (compare_array f)) ==? (compare_array f))
	ln1 ln2 tl1 tl2 bl1 bl2
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
	((Pervasives.compare =? (compare_array f)) ==? (compare_array f))
	ln1 ln2 tl1 tl2 bl1 bl2
    | _ -> Pervasives.compare t1 t2

let rec compare_constr m n=
  compare_constr_int compare_constr m n
    
module OrderedConstr=
struct
  type t=constr
  let compare=compare_constr
end

module Hitem=
struct 
  type t=(global_reference * constr option)
  let compare (id1,co1) (id2,co2)=
    (Pervasives.compare 
     =? (fun oc1 oc2 ->
	   match oc1,oc2 with 
	       Some c1,Some c2 -> OrderedConstr.compare c1 c2
	     | _,_->Pervasives.compare oc1 oc2)) id1 id2 co1 co2
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

	
