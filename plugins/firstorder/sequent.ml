(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Names
open EConstr
open Formula
open Unify

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

type h_item = GlobRef.t * (int*Constr.t) option

module Hitem=
struct
  type t = h_item
  let compare (id1,co1) (id2,co2)=
    let c = Globnames.RefOrdered.compare id1 id2 in
    if c = 0 then
      let cmp (i1, c1) (i2, c2) =
        let c = Int.compare i1 i2 in
        if c = 0 then Constr.compare c1 c2 else c
      in
      Option.compare cmp co1 co2
    else c
end

module CM=Map.Make(Constr)

module History=Set.Make(Hitem)

let cm_add sigma typ nam cm=
  let typ = EConstr.to_constr ~abort_on_undefined_evars:false sigma typ in
  try
    let l=CM.find typ cm in CM.add typ (nam::l) cm
  with
      Not_found->CM.add typ [nam] cm

let cm_remove sigma typ nam cm=
  let typ = EConstr.to_constr ~abort_on_undefined_evars:false sigma typ in
  try
    let l=CM.find typ cm in
    let l0=List.filter (fun id-> not (GlobRef.equal id nam)) l in
      match l0 with
	  []->CM.remove typ cm
	| _ ->CM.add typ l0 cm
      with Not_found ->cm

module HP=Heap.Functional(OrderedFormula)

type t=
    {redexes:HP.t;
     context:(GlobRef.t list) CM.t;
     latoms:constr list;
     gl:types;
     glatom:constr option;
     cnt:counter;
     history:History.t;
     depth:int}

let deepen seq={seq with depth=seq.depth-1}

let record item seq={seq with history=History.add item seq.history}

let lookup sigma item seq=
  History.mem item seq.history ||
  match item with
      (_,None)->false
    | (id,Some (m, t))->
	let p (id2,o)=
	  match o with
	      None -> false
            | Some (m2, t2)-> GlobRef.equal id id2 && m2>m && more_general sigma (m2, EConstr.of_constr t2) (m, EConstr.of_constr t) in
	  History.exists p seq.history

let add_formula env sigma side nam t seq =
  match build_formula env sigma side nam t seq.cnt with
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
		   context=cm_add sigma f.constr nam seq.context}
	end
    | Right t->
	match side with
	    Concl ->
	      {seq with gl=t;glatom=Some t}
	  | _ ->
	      {seq with
		 context=cm_add sigma t nam seq.context;
		 latoms=t::seq.latoms}

let re_add_formula_list sigma lf seq=
  let do_one f cm=
    if f.id == dummy_id then cm
    else cm_add sigma f.constr f.id cm in
  {seq with
     redexes=List.fold_right HP.add lf seq.redexes;
     context=List.fold_right do_one lf seq.context}

let find_left sigma t seq=List.hd (CM.find (EConstr.to_constr ~abort_on_undefined_evars:false sigma t) seq.context)

(*let rev_left seq=
  try
    let lpat=(HP.maximum seq.redexes).pat in
      left_reversible lpat
  with Heap.EmptyHeap -> false
*)

let rec take_formula sigma seq=
  let hd=HP.maximum seq.redexes
  and hp=HP.remove seq.redexes in
    if hd.id == dummy_id then
      let nseq={seq with redexes=hp} in
	if seq.gl==hd.constr then
	  hd,nseq
	else
	  take_formula sigma nseq (* discarding deprecated goal *)
    else
      hd,{seq with
	    redexes=hp;
	    context=cm_remove sigma hd.constr hd.id seq.context}

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
    | GlobRef.IndRef ind ->
        List.init (Inductiveops.nconstructors ind)
          (fun i -> GlobRef.ConstructRef (ind,i+1))
    | gr ->
	[gr])

let extend_with_ref_list env sigma l seq =
  let l = expand_constructor_hints l in
  let f gr (seq, sigma) =
    let sigma, c = Evd.fresh_global env sigma gr in
    let sigma, typ= Typing.type_of env sigma c in
      (add_formula env sigma Hyp gr typ seq, sigma) in
    List.fold_right f l (seq, sigma)

open Hints

let extend_with_auto_hints env sigma l seq =
  let seqref=ref seq in
  let f p_a_t =
    match repr_hint p_a_t.code with
	Res_pf (c,_) | Give_exact (c,_)
      | Res_pf_THEN_trivial_fail (c,_) ->
          let (c, _, _) = c in
	  (try
	     let (gr, _) = Termops.global_of_constr sigma c in
	     let typ=(Typing.unsafe_type_of env sigma c) in
	       seqref:=add_formula env sigma Hint gr typ !seqref
	   with Not_found->())
      | _-> () in
  let g _ _ l = List.iter f l in
  let h dbname=
    let hdb=
      try
	searchtable_map dbname
      with Not_found->
	user_err Pp.(str ("Firstorder: "^dbname^" : No such Hint database")) in
      Hint_db.iter g hdb in
    List.iter h l;
    !seqref, sigma (*FIXME: forgetting about universes*)

let print_cmap map=
  let print_entry c l s=
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let xc=Constrextern.extern_constr false env sigma (EConstr.of_constr c) in
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


