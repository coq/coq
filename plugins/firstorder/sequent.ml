(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

type h_item = GlobRef.t * Unify.Item.t option

module Hitem=
struct
  type t = h_item
  let compare (id1,co1) (id2,co2)=
    let c = GlobRef.CanOrd.compare id1 id2 in
    if c = 0 then Option.compare Unify.Item.compare co1 co2
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

type seqgoal = GoalTerm of EConstr.t | GoalAtom of atom

type t=
    {redexes:HP.t;
     context:(GlobRef.t list) CM.t;
     latoms:atom list;
     gl: seqgoal;
     cnt:counter;
     history:History.t;
     depth:int}

let has_fuel seq = seq.depth > 0

let iter_redexes f seq = HP.iter f seq.redexes

let deepen seq={seq with depth=seq.depth-1}

let record item seq={seq with history=History.add item seq.history}

let lookup env sigma item seq=
  History.mem item seq.history ||
  match item with
      (_,None)->false
    | (id,Some i1)->
        let p (id2,o)=
          match o with
              None -> false
            | Some i2 -> GlobRef.equal id id2 && more_general env sigma i2 i1 in
          History.exists p seq.history

let add_formula ~flags env sigma side nam t seq =
  match build_formula ~flags env sigma side nam t seq.cnt with
      Left f->
        begin
          match side with
              Concl ->
                {seq with
                   redexes=HP.add f seq.redexes;
                   gl = GoalTerm f.constr }
            | _ ->
              let nam = match nam with GoalId -> assert false | FormulaId id -> id in
                {seq with
                   redexes=HP.add f seq.redexes;
                   context=cm_add sigma f.constr nam seq.context}
        end
    | Right t->
        match side with
            Concl ->
              {seq with gl = GoalAtom t}
          | _ ->
            let nam = match nam with GoalId -> assert false | FormulaId id -> id in
              {seq with
                 context=cm_add sigma (repr_atom t) nam seq.context;
                 latoms=t::seq.latoms}

let re_add_formula_list sigma lf seq=
  let do_one f cm = match f.id with
  | GoalId -> cm
  | FormulaId id -> cm_add sigma f.constr id cm
  in
  {seq with
     redexes=List.fold_right HP.add lf seq.redexes;
     context=List.fold_right do_one lf seq.context}

let find_left sigma t seq=List.hd (CM.find (EConstr.to_constr ~abort_on_undefined_evars:false sigma t) seq.context)

let find_goal sigma seq =
  let t = match seq.gl with GoalAtom a -> repr_atom a | GoalTerm t -> t in
  find_left sigma t seq

let rec take_formula sigma seq=
  let hd=HP.maximum seq.redexes
  and hp=HP.remove seq.redexes in
  match hd.id with
  | GoalId ->
      let nseq={seq with redexes=hp} in
        if (match seq.gl with GoalAtom a -> repr_atom a | GoalTerm t -> t) == hd.constr then
          hd,nseq
        else
          take_formula sigma nseq (* discarding deprecated goal *)
  | FormulaId id ->
      hd,{seq with
            redexes=hp;
            context=cm_remove sigma hd.constr id seq.context}

let empty_seq depth=
  {redexes=HP.empty;
   context=CM.empty;
   latoms=[];
   gl= GoalTerm (mkMeta 1);
   cnt=newcnt ();
   history=History.empty;
   depth=depth}

let make_simple_atoms seq =
  let ratoms=
    match seq.gl with
    | GoalAtom t -> [t]
    | GoalTerm _ -> []
  in {negative=seq.latoms;positive=ratoms}

let expand_constructor_hints =
  List.map_append (function
    | GlobRef.IndRef ind ->
        List.init (Inductiveops.nconstructors (Global.env()) ind)
          (fun i -> GlobRef.ConstructRef (ind,i+1))
    | gr ->
        [gr])

let extend_with_ref_list ~flags env sigma l seq =
  let l = expand_constructor_hints l in
  let f gr (seq, sigma) =
    let sigma, c = Evd.fresh_global env sigma gr in
    let sigma, typ= Typing.type_of env sigma c in
      (add_formula ~flags env sigma Hyp (FormulaId gr) typ seq, sigma) in
    List.fold_right f l (seq, sigma)

open Hints

let extend_with_auto_hints ~flags env sigma l seq =
  let f (seq,sigma) p_a_t =
    match FullHint.repr p_a_t with
    | Res_pf c | Give_exact c
    | Res_pf_THEN_trivial_fail c ->
      let c = snd @@ hint_as_term c in
      (match  EConstr.destRef sigma c with
       | exception Constr.DestKO -> seq, sigma
       | gr, _ ->
         let sigma, typ = Typing.type_of env sigma c in
         add_formula ~flags env sigma Hint (FormulaId gr) typ seq, sigma)
    | _ -> seq, sigma
  in
  let h acc dbname =
    let hdb =
      try
        searchtable_map dbname
      with Not_found->
        user_err Pp.(str ("Firstorder: "^dbname^" : No such Hint database"))
    in
    Hint_db.fold (fun _ _ l acc -> List.fold_left f acc l) hdb acc
  in
  List.fold_left h (seq,sigma) l

(* For debug *)
let _print_cmap map=
  let print_entry c l s=
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let xc=Constrextern.extern_constr env sigma (EConstr.of_constr c) in
      str "| " ++
      prlist Printer.pr_global l ++
      str " : " ++
      Ppconstr.pr_constr_expr env sigma xc ++
      cut () ++
      s in
    (v 0
             (str "-----" ++
              cut () ++
              CM.fold print_entry map (mt ()) ++
              str "-----"))
