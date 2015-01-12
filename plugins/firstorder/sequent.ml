(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Errors
open Util
open Formula
open Unify
open Tacmach
open Globnames
open Pp

let newcnt ()=
  let cnt=ref (-1) in
    fun b->if b then incr cnt;!cnt

let priority = (* pure heuristics, <=0 for non reversible *)
  function
      Right rf->
	begin
	  match rf with
	      Rarrow               -> 100
	    | Rand                 ->  40
	    | Ror                  -> -15
	    | Rfalse               -> -50
	    | Rforall              -> 100
	    | Rexists (_,_,_)      -> -29
	end
    | Left lf ->
	match lf with
	    Lfalse                 -> 999
	  | Land _                 ->  90
	  | Lor _                  ->  40
	  | Lforall (_,_,_)        -> -30
	  | Lexists _              ->  60
	  | LA(_,lap) ->
	      match lap with
		  LLatom           ->   0
		| LLfalse (_,_)    -> 100
		| LLand (_,_)      ->  80
		| LLor (_,_)       ->  70
		| LLforall _       -> -20
		| LLexists (_,_)   ->  50
		| LLarrow  (_,_,_) -> -10

module OrderedFormula=
struct
  type t=Formula.t
  let compare e1 e2=
	(priority e1.pat) - (priority e2.pat)
end

module OrderedConstr=
struct
  type t=constr
  let compare=constr_ord
end

type h_item = global_reference * (int*constr) option

module Hitem=
struct
  type t = h_item
  let compare (id1,co1) (id2,co2)=
    let c = Globnames.RefOrdered.compare id1 id2 in
    if c = 0 then
      let cmp (i1, c1) (i2, c2) =
        let c = Int.compare i1 i2 in
        if c = 0 then OrderedConstr.compare c1 c2 else c
      in
      Option.compare cmp co1 co2
    else c
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
    let l0=List.filter (fun id-> not (Globnames.eq_gr id nam)) l in
      match l0 with
	  []->CM.remove typ cm
	| _ ->CM.add typ l0 cm
      with Not_found ->cm

module HP=Heap.Functional(OrderedFormula)

type t=
    {redexes:HP.t;
     context:(global_reference list) CM.t;
     latoms:constr list;
     gl:types;
     glatom:constr option;
     cnt:counter;
     history:History.t;
     depth:int}

let deepen seq={seq with depth=seq.depth-1}

let record item seq={seq with history=History.add item seq.history}

let lookup item seq=
  History.mem item seq.history ||
  match item with
      (_,None)->false
    | (id,Some ((m,t) as c))->
	let p (id2,o)=
	  match o with
	      None -> false
	    | Some ((m2,t2) as c2)-> Globnames.eq_gr id id2 && m2>m && more_general c2 c in
	  History.exists p seq.history

let add_formula side nam t seq gl=
  match build_formula side nam t gl seq.cnt with
      Left f->
	begin
	  match side with
	      Concl ->
		{seq with
		   redexes=HP.add f seq.redexes;
		   gl=f.constr;
		   glatom=None}
	    | _ ->
		{seq with
		   redexes=HP.add f seq.redexes;
		   context=cm_add f.constr nam seq.context}
	end
    | Right t->
	match side with
	    Concl ->
	      {seq with gl=t;glatom=Some t}
	  | _ ->
	      {seq with
		 context=cm_add t nam seq.context;
		 latoms=t::seq.latoms}

let re_add_formula_list lf seq=
  let do_one f cm=
    if f.id == dummy_id then cm
    else cm_add f.constr f.id cm in
  {seq with
     redexes=List.fold_right HP.add lf seq.redexes;
     context=List.fold_right do_one lf seq.context}

let find_left t seq=List.hd (CM.find t seq.context)

(*let rev_left seq=
  try
    let lpat=(HP.maximum seq.redexes).pat in
      left_reversible lpat
  with Heap.EmptyHeap -> false
*)

let rec take_formula seq=
  let hd=HP.maximum seq.redexes
  and hp=HP.remove seq.redexes in
    if hd.id == dummy_id then
      let nseq={seq with redexes=hp} in
	if seq.gl==hd.constr then
	  hd,nseq
	else
	  take_formula nseq (* discarding deprecated goal *)
    else
      hd,{seq with
	    redexes=hp;
	    context=cm_remove hd.constr hd.id seq.context}

let empty_seq depth=
  {redexes=HP.empty;
   context=CM.empty;
   latoms=[];
   gl=(mkMeta 1);
   glatom=None;
   cnt=newcnt ();
   history=History.empty;
   depth=depth}

let expand_constructor_hints =
  List.map_append (function
    | IndRef ind ->
        List.init (Inductiveops.nconstructors ind)
          (fun i -> ConstructRef (ind,i+1))
    | gr ->
	[gr])

let extend_with_ref_list l seq gl =
  let l = expand_constructor_hints l in
  let f gr (seq,gl) =
    let gl, c = pf_eapply Evd.fresh_global gl gr in
    let typ=(pf_type_of gl c) in
      (add_formula Hyp gr typ seq gl,gl) in
    List.fold_right f l (seq,gl)

open Hints

let extend_with_auto_hints l seq gl=
  let seqref=ref seq in
  let f p_a_t =
    match p_a_t.code with
	Res_pf (c,_) | Give_exact (c,_)
      | Res_pf_THEN_trivial_fail (c,_) ->
	  (try
	     let gr = global_of_constr c in
	     let typ=(pf_type_of gl c) in
	       seqref:=add_formula Hint gr typ !seqref gl
	   with Not_found->())
      | _-> () in
  let g _ _ l = List.iter f l in
  let h dbname=
    let hdb=
      try
	searchtable_map dbname
      with Not_found->
	error ("Firstorder: "^dbname^" : No such Hint database") in
      Hint_db.iter g hdb in
    List.iter h l;
    !seqref, gl (*FIXME: forgetting about universes*)

let print_cmap map=
  let print_entry c l s=
    let xc=Constrextern.extern_constr false (Global.env ()) Evd.empty c in
      str "| " ++
      prlist Printer.pr_global l ++
      str " : " ++
      Ppconstr.pr_constr_expr xc ++
      cut () ++
      s in
    (v 0
	     (str "-----" ++
	      cut () ++
	      CM.fold print_entry map (mt ()) ++
	      str "-----"))


