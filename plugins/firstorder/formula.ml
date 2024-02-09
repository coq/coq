(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Hipattern
open Names
open Constr
open EConstr
open Vars
open Util
open Declarations

module RelDecl = Context.Rel.Declaration

type flags = {
  qflag : bool;
  reds : RedFlags.reds;
}

let (=?) f g i1 i2 j1 j2=
  let c=f i1 i2 in
    if Int.equal c 0 then g j1 j2 else c

let (==?) fg h i1 i2 j1 j2 k1 k2=
  let c=fg i1 i2 j1 j2 in
    if Int.equal c 0 then h k1 k2 else c

type ('a,'b) sum = Left of 'a | Right of 'b

type counter = bool -> metavariable

type atom = { atom : constr }

let repr_atom a = a.atom

exception Is_atom of atom

let meta_succ m = m+1

let rec nb_prod_after n c=
  match Constr.kind c with
    | Prod (_,_,b) ->if n>0 then nb_prod_after (n-1) b else
        1+(nb_prod_after 0 b)
    | _ -> 0

let construct_nhyps env ind =
  let nparams = (fst (Global.lookup_inductive (fst ind))).mind_nparams in
  let constr_types = Inductiveops.arities_of_constructors env ind in
  let hyp = nb_prod_after nparams in
    Array.map hyp constr_types

(* indhyps builds the array of arrays of constructor hyps for (ind largs)*)
let ind_hyps env sigma nevar ind largs =
  let types= Inductiveops.arities_of_constructors env ind in
  let myhyps t =
    let t = EConstr.of_constr t in
    let nparam_decls = Context.Rel.length (fst (Global.lookup_inductive (fst ind))).mind_params_ctxt in
    let t1=Termops.prod_applist_decls sigma nparam_decls t largs in
    let t2=snd (decompose_prod_n_decls sigma nevar t1) in
      fst (decompose_prod_decls sigma t2) in
    Array.map myhyps types

let special_nf ~flags env sigma t =
  Reductionops.clos_norm_flags flags.reds env sigma t

let special_whd ~flags env sigma t =
  Reductionops.clos_whd_flags flags.reds env sigma t

type kind_of_formula=
    Arrow of constr*constr
  | False of pinductive*constr list
  | And of pinductive*constr list*bool
  | Or of pinductive*constr list*bool
  | Exists of pinductive*constr list
  | Forall of constr*constr
  | Atom of atom

let pop t = Vars.lift (-1) t

let kind_of_formula ~flags env sigma term =
  let normalize = special_nf ~flags env sigma in
  let cciterm = special_whd ~flags env sigma term in
    match match_with_imp_term env sigma cciterm with
        Some (a,b)-> Arrow (a, pop b)
      |_->
         match match_with_forall_term env sigma cciterm with
             Some (_,a,b)-> Forall (a, b)
           |_->
              match match_with_nodep_ind env sigma cciterm with
                  Some (i,l,n)->
                    let ind,u=EConstr.destInd sigma i in
                    let u = EConstr.EInstance.kind sigma u in
                    let (mib,mip) = Global.lookup_inductive ind in
                    let nconstr=Array.length mip.mind_consnames in
                      if Int.equal nconstr 0 then
                        False((ind,u),l)
                      else
                        let has_realargs=(n>0) in
                        let is_trivial=
                          let is_constant n = Int.equal n 0 in
                            Array.exists is_constant mip.mind_consnrealargs in
                          if Inductiveops.mis_is_recursive (ind,mib,mip) ||
                            (has_realargs && not is_trivial)
                          then
                            Atom { atom = cciterm }
                          else
                            if Int.equal nconstr 1 then
                              And((ind,u),l,is_trivial)
                            else
                              Or((ind,u),l,is_trivial)
                | _ ->
                    match match_with_sigma_type env sigma cciterm with
                        Some (i,l)->
                          let (ind, u) = EConstr.destInd sigma i in
                          let u = EConstr.EInstance.kind sigma u in
                          Exists((ind, u), l)
                      |_-> Atom { atom = normalize cciterm }

type atoms = {positive:atom list;negative:atom list}

type _ side =
| Hyp : bool -> [ `Hyp ] side (* true if treated as hint *)
| Concl : [ `Goal ] side

let no_atoms = (false,{positive=[];negative=[]})

let build_atoms (type a) ~flags env sigma metagen (side : a side) cciterm =
  let trivial =ref false
  and positive=ref []
  and negative=ref [] in
  let normalize=special_nf ~flags env sigma in
  let rec build_rec subst polarity cciterm=
    match kind_of_formula ~flags env sigma cciterm with
        False(_,_)->if not polarity then trivial:=true
      | Arrow (a,b)->
          build_rec subst (not polarity) a;
          build_rec subst polarity b
      | And(i,l,b) | Or(i,l,b)->
          if b then
            begin
              let unsigned= { atom = normalize (substnl subst 0 cciterm) } in
                if polarity then
                  positive:= unsigned :: !positive
                else
                  negative:= unsigned :: !negative
            end;
          let v = ind_hyps env sigma 0 i l in
          let g i _ decl =
            build_rec subst polarity (lift i (RelDecl.get_type decl)) in
          let f l =
            List.fold_left_i g (1-(List.length l)) () l in
            if polarity && (* we have a constant constructor *)
              Array.exists (function []->true|_->false) v
            then trivial:=true;
            Array.iter f v
      | Exists(i,l)->
          let var=mkMeta (metagen true) in
          let v =(ind_hyps env sigma 1 i l).(0) in
          let g i _ decl =
            build_rec (var::subst) polarity (lift i (RelDecl.get_type decl)) in
            List.fold_left_i g (2-(List.length l)) () v
      | Forall(_,b)->
          let var=mkMeta (metagen true) in
            build_rec (var::subst) polarity b
      | Atom t->
          let unsigned= { atom = substnl subst 0 t.atom } in
            if not (isMeta sigma unsigned.atom) then (* discarding wildcard atoms *)
              if polarity then
                positive:= unsigned :: !positive
              else
                negative:= unsigned :: !negative in
    begin
      match side with
          Concl     -> build_rec [] true cciterm
        | Hyp false -> build_rec [] false cciterm
        | Hyp true  ->
            let rels,head=decompose_prod sigma cciterm in
            let subst=List.rev_map (fun _->mkMeta (metagen true)) rels in
              build_rec subst false head;trivial:=false (* special for hints *)
    end;
    (!trivial,
     {positive= !positive;
      negative= !negative})

type right_pattern =
    Rarrow
  | Rand
  | Ror
  | Rfalse
  | Rforall
  | Rexists of metavariable*constr*bool

type left_arrow_pattern=
    LLatom
  | LLfalse of pinductive*constr list
  | LLand of pinductive*constr list
  | LLor of pinductive*constr list
  | LLforall of constr
  | LLexists of pinductive*constr list
  | LLarrow of constr*constr*constr

type left_pattern=
    Lfalse
  | Land of pinductive
  | Lor of pinductive
  | Lforall of metavariable*constr*bool
  | Lexists of pinductive
  | LA of constr*left_arrow_pattern

type _ identifier =
| GoalId : [ `Goal ] identifier
| FormulaId : GlobRef.t -> [ `Hyp ] identifier

let goal_id = GoalId
let formula_id env gr = FormulaId (Environ.QGlobRef.canonize env gr)

type _ pattern =
| LeftPattern : left_pattern -> [ `Hyp ] pattern
| RightPattern : right_pattern -> [ `Goal ] pattern

type 'a t = {
  id : 'a identifier;
  constr : constr;
  pat : 'a pattern;
  atoms : atoms;
}

type any_formula = AnyFormula : 'a t -> any_formula

let build_formula (type a) ~flags env sigma (side : a side) (nam : a identifier) typ metagen : (a t, atom) sum =
  let normalize = special_nf ~flags env sigma in
    try
      let m=meta_succ(metagen false) in
      let trivial,atoms=
        if flags.qflag then
          build_atoms ~flags env sigma metagen side typ
        else no_atoms in
      let pattern : a pattern =
        match side with
            Concl ->
              let pat=
                match kind_of_formula ~flags env sigma typ with
                    False(_,_)        -> Rfalse
                  | Atom a       -> raise (Is_atom a)
                  | And(_,_,_)        -> Rand
                  | Or(_,_,_)         -> Ror
                  | Exists (i,l) ->
                      let d = RelDecl.get_type (List.last (ind_hyps env sigma 0 i l).(0)) in
                        Rexists(m,d,trivial)
                  | Forall (_,a) -> Rforall
                  | Arrow (a,b) -> Rarrow in
                RightPattern pat
          | Hyp _ ->
              let pat=
                match kind_of_formula ~flags env sigma typ with
                    False(i,_)        ->  Lfalse
                  | Atom a       ->  raise (Is_atom a)
                  | And(i,_,b)         ->
                      if b then
                        let nftyp=normalize typ in raise (Is_atom { atom = nftyp })
                      else Land i
                  | Or(i,_,b)          ->
                      if b then
                        let nftyp=normalize typ in raise (Is_atom { atom = nftyp })
                      else Lor i
                  | Exists (ind,_) ->  Lexists ind
                  | Forall (d,_) ->
                      Lforall(m,d,trivial)
                  | Arrow (a,b) ->
                      let nfa=normalize a in
                        LA (nfa,
                            match kind_of_formula ~flags env sigma a with
                                False(i,l)-> LLfalse(i,l)
                              | Atom t->     LLatom
                              | And(i,l,_)-> LLand(i,l)
                              | Or(i,l,_)->  LLor(i,l)
                              | Arrow(a,c)-> LLarrow(a,c,b)
                              | Exists(i,l)->LLexists(i,l)
                              | Forall(_,_)->LLforall a) in
                LeftPattern pat
      in
        Left {id=nam;
              constr=normalize typ;
              pat=pattern;
              atoms=atoms}
    with Is_atom a-> Right a (* already in nf *)

