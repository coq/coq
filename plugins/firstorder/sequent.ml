(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Util
open Formula
open Unify
open Tacmach
open Names
open Libnames
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

let left_reversible lpat=(priority lpat)>0

module OrderedFormula=
struct
  type t=Formula.t
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
    | Var id1, Var id2 -> id_ord id1 id2
    | Sort s1, Sort s2 -> Pervasives.compare s1 s2
    | Cast (c1,_,_), _ -> f c1 t2
    | _, Cast (c2,_,_) -> f t1 c2
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
    | Const c1, Const c2 -> kn_ord (canonical_con c1) (canonical_con c2)
    | Ind (spx, ix), Ind (spy, iy) ->
	let c = ix - iy in if c = 0 then kn_ord (canonical_mind spx) (canonical_mind spy) else c
    | Construct ((spx, ix), jx), Construct ((spy, iy), jy) ->
	let c = jx - jy in if c = 0 then
	  (let c = ix - iy in if c = 0 then kn_ord (canonical_mind spx) (canonical_mind spy) else c)
	else c
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
	((f =? f) ==? (compare_array f)) p1 p2 c1 c2 bl1 bl2
    | Fix (ln1,(_,tl1,bl1)), Fix (ln2,(_,tl2,bl2)) ->
	((Pervasives.compare =? (compare_array f)) ==? (compare_array f))
	ln1 ln2 tl1 tl2 bl1 bl2
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
	((Pervasives.compare =? (compare_array f)) ==? (compare_array f))
	ln1 ln2 tl1 tl2 bl1 bl2
    | Var _, (Rel _)
    | Meta _, (Rel _ | Var _)
    | Evar _, (Rel _ | Var _ | Meta _)
    | Sort _, (Rel _ | Var _ | Meta _ | Evar _)
    | Prod _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _)
    | Lambda _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _)
    | LetIn _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _)
    | App _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _ | LetIn _)
    | Const _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _)
    | Ind _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Const _)
    | Construct _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Const _ | Ind _)
    | Case _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Const _ | Ind _ | Construct _)
    | Fix _, (Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _ | Const _ | Ind _ | Construct _ | Case _)
    | CoFix _, _
      -> -1
    | Rel _, _ | Var _, _ | Meta _, _ | Evar _, _
    | Sort _, _ | Prod _, _
    | Lambda _, _ | LetIn _, _ | App _, _
    | Const _, _ | Ind _, _ | Construct _, _
    | Case _, _| Fix _, _
      -> 1

let rec compare_constr m n=
  compare_constr_int compare_constr m n

module OrderedConstr=
struct
  type t=constr
  let compare=compare_constr
end

type h_item = global_reference * (int*constr) option

module Hitem=
struct
  type t = h_item
  let compare (id1,co1) (id2,co2)=
    (Libnames.RefOrdered.compare
     =? (fun oc1 oc2 ->
	   match oc1,oc2 with
	       Some (m1,c1),Some (m2,c2) ->
		 ((-) =? OrderedConstr.compare) m1 m2 c1 c2
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
	    | Some ((m2,t2) as c2)->id=id2 && m2>m && more_general c2 c in
	  History.exists p seq.history

let rec add_formula side nam t seq gl=
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
let no_formula seq=
  seq.redexes=HP.empty

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
  list_map_append (function
    | IndRef ind ->
	list_tabulate (fun i -> ConstructRef (ind,i+1))
	  (Inductiveops.nconstructors ind)
    | gr ->
	[gr])

let extend_with_ref_list l seq gl=
  let l = expand_constructor_hints l in
  let f gr seq=
    let c=constr_of_global gr in
    let typ=(pf_type_of gl c) in
      add_formula Hyp gr typ seq gl in
    List.fold_right f l seq

open Auto

let extend_with_auto_hints l seq gl=
  let seqref=ref seq in
  let f p_a_t =
    match p_a_t.code with
	Res_pf (c,_) | Give_exact c
      | Res_pf_THEN_trivial_fail (c,_) ->
	  (try
	     let gr=global_of_constr c in
	     let typ=(pf_type_of gl c) in
	       seqref:=add_formula Hint gr typ !seqref gl
	   with Not_found->())
      | _-> () in
  let g _ l=List.iter f l in
  let h dbname=
    let hdb=
      try
	searchtable_map dbname
      with Not_found->
	error ("Firstorder: "^dbname^" : No such Hint database") in
      Hint_db.iter g hdb in
    List.iter h l;
    !seqref

let print_cmap map=
  let print_entry c l s=
    let xc=Constrextern.extern_constr false (Global.env ()) c in
      str "| " ++
      Util.prlist Printer.pr_global l ++
      str " : " ++
      Ppconstr.pr_constr_expr xc ++
      cut () ++
      s in
    msgnl (v 0
	     (str "-----" ++
	      cut () ++
	      CM.fold print_entry map (mt ()) ++
	      str "-----"))


