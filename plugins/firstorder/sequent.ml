(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open CErrors
open Names
open Formula
open Unify

let newcnt ()=
  let cnt=ref (-1) in
    fun b->if b then incr cnt;!cnt

let priority : type a. a pattern -> int = (* pure heuristics, <=0 for non reversible *)
  function
      RightPattern rf->
        begin
          match rf with
              Rarrow               -> 100
            | Rand                 ->  40
            | Ror                  -> -15
            | Rfalse               -> -50
            | Rforall              -> 100
            | Rexists (_,_,_)      -> -29
        end
    | LeftPattern lf ->
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
  type t=Formula.any_formula
  let compare (AnyFormula e1) (AnyFormula e2) =
        (priority e1.pat) - (priority e2.pat)
end

type h_item = GlobRef.t * Unify.Item.t option

let h_canonize env (hr, item) =
  (Environ.QGlobRef.canonize env hr, item)

module Hitem=
struct
  type t = h_item
  let compare (id1,co1) (id2,co2)=
    let c = GlobRef.UserOrd.compare id1 id2 in
    if c = 0 then Option.compare Unify.Item.compare co1 co2
    else c
end

module History=Set.Make(Hitem)

module Context :
sig
  type t
  val empty : t
  val find : Evd.evar_map -> atom -> t -> GlobRef.t
  val add : Evd.evar_map -> atom -> GlobRef.t -> t -> t
  val remove : Environ.env -> Evd.evar_map -> atom -> GlobRef.t -> t -> t
end =
struct

module Atom =
struct
  type t = atom
  let compare = compare_atom
end

module CM = Map.Make(Atom)

type t = GlobRef.t list CM.t

let empty = CM.empty

let find sigma t cm =
  List.hd (CM.find t cm)

let add sigma typ nam cm =
  try
    let l=CM.find typ cm in CM.add typ (nam::l) cm
  with
      Not_found->CM.add typ [nam] cm

let remove env sigma typ nam cm =
  try
    let l=CM.find typ cm in
    let l0=List.filter (fun id-> not (Environ.QGlobRef.equal env id nam)) l in
      match l0 with
          []->CM.remove typ cm
        | _ ->CM.add typ l0 cm
      with Not_found ->cm

end

module HP=Heap.Functional(OrderedFormula)

type seqgoal = GoalTerm of atom | GoalAtom of atom

type t=
    {redexes:HP.t;
     context:Context.t;
     state : Env.t;
     latoms:atom list;
     gl: seqgoal;
     cnt:counter;
     history:History.t;
     depth:int}

let has_fuel seq = seq.depth > 0

let iter_redexes f seq = HP.iter f seq.redexes

let deepen seq={seq with depth=seq.depth-1}

let record env item seq={seq with history=History.add (h_canonize env item) seq.history}

let lookup env sigma item seq=
  History.mem (h_canonize env item) seq.history ||
  match item with
      (_,None)->false
    | (id,Some i1)->
        let p (id2,o)=
          match o with
              None -> false
            | Some i2 -> Environ.QGlobRef.equal env id id2 && more_general env sigma i2 i1 in
          History.exists p seq.history

let add_concl ~flags env sigma t seq =
  match build_formula ~flags seq.state env sigma Concl goal_id t seq.cnt with
  | state, Left f ->
    {seq with redexes=HP.add (AnyFormula f) seq.redexes; gl = GoalTerm f.constr; state }
  | state, Right t ->
    {seq with gl = GoalAtom t; state}

let add_formula ~flags ~hint env sigma id t seq =
  let side = Hyp hint in
  match build_formula ~flags seq.state env sigma side (formula_id env id) t seq.cnt with
  | state, Left f ->
    {seq with
      redexes=HP.add (AnyFormula f) seq.redexes;
      context=Context.add sigma f.constr id seq.context;
      state}
  | state, Right t ->
    {seq with
      context=Context.add sigma t id seq.context;
      latoms=t::seq.latoms;
      state}

let re_add_formula_list sigma lf seq=
  let do_one (AnyFormula f) cm = match f.id with
  | GoalId -> cm
  | FormulaId id -> Context.add sigma f.constr id cm
  in
  {seq with
     redexes=List.fold_right HP.add lf seq.redexes;
     context=List.fold_right do_one lf seq.context}

let find_left sigma t seq = Context.find sigma t seq.context

let find_goal sigma seq =
  let t = match seq.gl with GoalAtom a -> a | GoalTerm t -> t in
  find_left sigma t seq

let rec take_formula env sigma seq=
  let hd = HP.maximum seq.redexes in
  let hp = HP.remove seq.redexes in
  let AnyFormula hd0 = hd in
  match hd0.id with
  | GoalId ->
    let nseq={seq with redexes=hp} in
    begin match seq.gl with
    | GoalTerm t when t == hd0.constr -> hd, nseq
    | GoalAtom _ | GoalTerm _ -> take_formula env sigma nseq (* discarding deprecated goal *)
    end
  | FormulaId id ->
      hd,{seq with
            redexes=hp;
            context=Context.remove env sigma hd0.constr id seq.context}

let empty_seq depth=
  {redexes=HP.empty;
   context=Context.empty;
   latoms=[];
   gl= GoalTerm hole_atom;
   cnt=newcnt ();
   history=History.empty;
   depth=depth;
   state=Env.empty}

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
      (add_formula ~flags ~hint:false env sigma gr typ seq, sigma) in
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
         add_formula ~flags ~hint:true env sigma gr typ seq, sigma)
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

let state seq = seq.state
