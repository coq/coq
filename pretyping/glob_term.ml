(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Errors
open Pp
open Util
open Names
open Sign
open Term
open Libnames
open Nametab
open Evd
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

(* locs here refers to the ident's location, not whole pat *)
(* the last argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name

let cases_pattern_loc = function
    PatVar(loc,_) -> loc
  | PatCstr(loc,_,_,_) -> loc

type patvar = identifier

type glob_sort = GProp of Term.contents | GType of Univ.universe option

type binding_kind = Lib.binding_kind = Explicit | Implicit

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (loc * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings

type 'a cast_type =
  | CastConv of cast_kind * 'a
  | CastCoerce (* Cast to a base type (eg, an underlying inductive type) *)

type glob_constr =
  | GRef of (loc * global_reference)
  | GVar of (loc * identifier)
  | GEvar of loc * existential_key * glob_constr list option
  | GPatVar of loc * (bool * patvar) (* Used for patterns only *)
  | GApp of loc * glob_constr * glob_constr list
  | GLambda of loc * name * binding_kind * glob_constr * glob_constr
  | GProd of loc * name * binding_kind * glob_constr * glob_constr
  | GLetIn of loc * name * glob_constr * glob_constr
  | GCases of loc * case_style * glob_constr option * tomatch_tuples * cases_clauses
  | GLetTuple of loc * name list * (name * glob_constr option) *
      glob_constr * glob_constr
  | GIf of loc * glob_constr * (name * glob_constr option) * glob_constr * glob_constr
  | GRec of loc * fix_kind * identifier array * glob_decl list array *
      glob_constr array * glob_constr array
  | GSort of loc * glob_sort
  | GHole of (loc * hole_kind)
  | GCast of loc * glob_constr * glob_constr cast_type

and glob_decl = name * binding_kind * glob_constr option * glob_constr

and fix_recursion_order = GStructRec | GWfRec of glob_constr | GMeasureRec of glob_constr * glob_constr option

and fix_kind =
  | GFix of ((int option * fix_recursion_order) array * int)
  | GCoFix of int

and predicate_pattern =
    name * (loc * inductive * name list) option

and tomatch_tuple = (glob_constr * predicate_pattern)

and tomatch_tuples = tomatch_tuple list

and cases_clause = (loc * identifier list * cases_pattern list * glob_constr)

and cases_clauses = cases_clause list

let cases_predicate_names tml =
  List.flatten (List.map (function
    | (tm,(na,None)) -> [na]
    | (tm,(na,Some (_,_,nal))) -> na::nal) tml)

let mkGApp loc p t =
  match p with
  | GApp (loc,f,l) -> GApp (loc,f,l@[t])
  | _ -> GApp (loc,p,[t])

let map_glob_decl_left_to_right f (na,k,obd,ty) = 
  let comp1 = Option.map f obd in
  let comp2 = f ty in
  (na,k,comp1,comp2)

let map_glob_constr_left_to_right f = function
  | GApp (loc,g,args) -> 
      let comp1 = f g in 
      let comp2 = Util.list_map_left f args in 
      GApp (loc,comp1,comp2)
  | GLambda (loc,na,bk,ty,c) -> 
      let comp1 = f ty in 
      let comp2 = f c in 
      GLambda (loc,na,bk,comp1,comp2)
  | GProd (loc,na,bk,ty,c) -> 
      let comp1 = f ty in 
      let comp2 = f c in 
      GProd (loc,na,bk,comp1,comp2)
  | GLetIn (loc,na,b,c) -> 
      let comp1 = f b in 
      let comp2 = f c in 
      GLetIn (loc,na,comp1,comp2)
  | GCases (loc,sty,rtntypopt,tml,pl) ->
      let comp1 = Option.map f rtntypopt in 
      let comp2 = Util.list_map_left (fun (tm,x) -> (f tm,x)) tml in
      let comp3 = Util.list_map_left (fun (loc,idl,p,c) -> (loc,idl,p,f c)) pl in
      GCases (loc,sty,comp1,comp2,comp3)
  | GLetTuple (loc,nal,(na,po),b,c) ->
      let comp1 = Option.map f po in
      let comp2 = f b in
      let comp3 = f c in 
      GLetTuple (loc,nal,(na,comp1),comp2,comp3)
  | GIf (loc,c,(na,po),b1,b2) ->
      let comp1 = Option.map f po in
      let comp2 = f b1 in
      let comp3 = f b2 in
      GIf (loc,f c,(na,comp1),comp2,comp3)
  | GRec (loc,fk,idl,bl,tyl,bv) ->
      let comp1 = Array.map (Util.list_map_left (map_glob_decl_left_to_right f)) bl in
      let comp2 = Array.map f tyl in
      let comp3 = Array.map f bv in
      GRec (loc,fk,idl,comp1,comp2,comp3)
  | GCast (loc,c,k) -> 
      let comp1 = f c in
      let comp2 = match k with CastConv (k,t) -> CastConv (k, f t) | x -> x in
      GCast (loc,comp1,comp2)
  | (GVar _ | GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) as x -> x

let map_glob_constr = map_glob_constr_left_to_right

(*
let name_app f e = function
  | Name id -> let (id, e) = f id e in (Name id, e)
  | Anonymous -> Anonymous, e

let fold_ident g idl e =
  let (idl,e) =
    Array.fold_right
      (fun id (idl,e) -> let id,e = g id e in (id::idl,e)) idl ([],e)
  in (Array.of_list idl,e)

let map_glob_constr_with_binders_loc loc g f e = function
  | GVar (_,id) -> GVar (loc,id)
  | GApp (_,a,args) -> GApp (loc,f e a, List.map (f e) args)
  | GLambda (_,na,ty,c) ->
      let na,e = name_app g e na in GLambda (loc,na,f e ty,f e c)
  | GProd (_,na,ty,c) ->
      let na,e = name_app g e na in GProd (loc,na,f e ty,f e c)
  | GLetIn (_,na,b,c) ->
      let na,e = name_app g e na in GLetIn (loc,na,f e b,f e c)
  | GCases (_,tyopt,tml,pl) ->
      (* We don't modify pattern variable since we don't traverse patterns *)
      let g' id e = snd (g id e) in
      let h (_,idl,p,c) = (loc,idl,p,f (List.fold_right g' idl e) c) in
      GCases
	(loc,Option.map (f e) tyopt,List.map (f e) tml, List.map h pl)
  | GRec (_,fk,idl,tyl,bv) ->
      let idl',e' = fold_ident g idl e in
      GRec (loc,fk,idl',Array.map (f e) tyl,Array.map (f e') bv)
  | GCast (_,c,t) -> GCast (loc,f e c,f e t)
  | GSort (_,x) -> GSort (loc,x)
  | GHole (_,x)  -> GHole (loc,x)
  | GRef (_,x) -> GRef (loc,x)
  | GEvar (_,x,l) -> GEvar (loc,x,l)
  | GPatVar (_,x) -> GPatVar (loc,x)
*)

let fold_glob_constr f acc =
  let rec fold acc = function
  | GVar _ -> acc
  | GApp (_,c,args) -> List.fold_left fold (fold acc c) args
  | GLambda (_,_,_,b,c) | GProd (_,_,_,b,c) | GLetIn (_,_,b,c) ->
      fold (fold acc b) c
  | GCases (_,_,rtntypopt,tml,pl) ->
      List.fold_left fold_pattern
	(List.fold_left fold (Option.fold_left fold acc rtntypopt) (List.map fst tml))
	pl
    | GLetTuple (_,_,rtntyp,b,c) ->
	fold (fold (fold_return_type acc rtntyp) b) c
    | GIf (_,c,rtntyp,b1,b2) ->
	fold (fold (fold (fold_return_type acc rtntyp) c) b1) b2
    | GRec (_,_,_,bl,tyl,bv) ->
	let acc = Array.fold_left
	  (List.fold_left (fun acc (na,k,bbd,bty) ->
	    fold (Option.fold_left fold acc bbd) bty)) acc bl in
	Array.fold_left fold (Array.fold_left fold acc tyl) bv
    | GCast (_,c,k) -> fold (match k with CastConv (_, t) -> fold acc t | CastCoerce -> acc) c
    | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> acc

  and fold_pattern acc (_,idl,p,c) = fold acc c

  and fold_return_type acc (na,tyopt) = Option.fold_left fold acc tyopt

  in fold acc

let iter_glob_constr f = fold_glob_constr (fun () -> f) ()

let occur_glob_constr id =
  let rec occur = function
    | GVar (loc,id') -> id = id'
    | GApp (loc,f,args) -> (occur f) or (List.exists occur args)
    | GLambda (loc,na,bk,ty,c) -> (occur ty) or ((na <> Name id) & (occur c))
    | GProd (loc,na,bk,ty,c) -> (occur ty) or ((na <> Name id) & (occur c))
    | GLetIn (loc,na,b,c) -> (occur b) or ((na <> Name id) & (occur c))
    | GCases (loc,sty,rtntypopt,tml,pl) ->
	(occur_option rtntypopt)
        or (List.exists (fun (tm,_) -> occur tm) tml)
	or (List.exists occur_pattern pl)
    | GLetTuple (loc,nal,rtntyp,b,c) ->
	occur_return_type rtntyp id
        or (occur b) or (not (List.mem (Name id) nal) & (occur c))
    | GIf (loc,c,rtntyp,b1,b2) ->
	occur_return_type rtntyp id or (occur c) or (occur b1) or (occur b2)
    | GRec (loc,fk,idl,bl,tyl,bv) ->
        not (array_for_all4 (fun fid bl ty bd ->
          let rec occur_fix = function
              [] -> not (occur ty) && (fid=id or not(occur bd))
            | (na,k,bbd,bty)::bl ->
                not (occur bty) &&
                (match bbd with
                    Some bd -> not (occur bd)
                  | _ -> true) &&
                (na=Name id or not(occur_fix bl)) in
          occur_fix bl)
          idl bl tyl bv)
    | GCast (loc,c,k) -> (occur c) or (match k with CastConv (_, t) -> occur t | CastCoerce -> false)
    | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> false

  and occur_pattern (loc,idl,p,c) = not (List.mem id idl) & (occur c)

  and occur_option = function None -> false | Some p -> occur p

  and occur_return_type (na,tyopt) id = na <> Name id & occur_option tyopt

  in occur


let add_name_to_ids set na =
  match na with
    | Anonymous -> set
    | Name id -> Idset.add id set

let free_glob_vars  =
  let rec vars bounded vs = function
    | GVar (loc,id') -> if Idset.mem id' bounded then vs else Idset.add id' vs
    | GApp (loc,f,args) -> List.fold_left (vars bounded) vs (f::args)
    | GLambda (loc,na,_,ty,c) | GProd (loc,na,_,ty,c) | GLetIn (loc,na,ty,c) ->
	let vs' = vars bounded vs ty in
	let bounded' = add_name_to_ids bounded na in
       vars bounded' vs' c
    | GCases (loc,sty,rtntypopt,tml,pl) ->
	let vs1 = vars_option bounded vs rtntypopt in
	let vs2 = List.fold_left (fun vs (tm,_) -> vars bounded vs tm) vs1 tml in
	List.fold_left (vars_pattern bounded) vs2 pl
    | GLetTuple (loc,nal,rtntyp,b,c) ->
	let vs1 = vars_return_type bounded vs rtntyp in
	let vs2 = vars bounded vs1 b in
	let bounded' = List.fold_left add_name_to_ids bounded nal in
	vars bounded' vs2 c
    | GIf (loc,c,rtntyp,b1,b2) ->
	let vs1 = vars_return_type bounded vs rtntyp in
	let vs2 = vars bounded vs1 c in
	let vs3 = vars bounded vs2 b1 in
	vars bounded vs3 b2
    | GRec (loc,fk,idl,bl,tyl,bv) ->
	let bounded' = Array.fold_right Idset.add idl bounded in
	let vars_fix i vs fid =
	  let vs1,bounded1 =
	    List.fold_left
	      (fun (vs,bounded) (na,k,bbd,bty) ->
		 let vs' = vars_option bounded vs bbd in
		 let vs'' = vars bounded vs' bty in
		 let bounded' = add_name_to_ids bounded na in
		 (vs'',bounded')
	      )
	      (vs,bounded')
	      bl.(i)
	  in
	  let vs2 = vars bounded1 vs1 tyl.(i) in
	  vars bounded1 vs2 bv.(i)
	in
	array_fold_left_i vars_fix vs idl
    | GCast (loc,c,k) -> let v = vars bounded vs c in
	(match k with CastConv (_,t) -> vars bounded v t | _ -> v)
    | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> vs

  and vars_pattern bounded vs (loc,idl,p,c) =
    let bounded' = List.fold_right Idset.add idl bounded  in
    vars bounded' vs c

  and vars_option bounded vs = function None -> vs | Some p -> vars bounded vs p

  and vars_return_type bounded vs (na,tyopt) =
    let bounded' = add_name_to_ids bounded na in
    vars_option bounded' vs tyopt
  in
  fun rt ->
    let vs = vars Idset.empty Idset.empty rt in
    Idset.elements vs


let loc_of_glob_constr = function
  | GRef (loc,_) -> loc
  | GVar (loc,_) -> loc
  | GEvar (loc,_,_) -> loc
  | GPatVar (loc,_) -> loc
  | GApp (loc,_,_) -> loc
  | GLambda (loc,_,_,_,_) -> loc
  | GProd (loc,_,_,_,_) -> loc
  | GLetIn (loc,_,_,_) -> loc
  | GCases (loc,_,_,_,_) -> loc
  | GLetTuple (loc,_,_,_,_) -> loc
  | GIf (loc,_,_,_,_) -> loc
  | GRec (loc,_,_,_,_,_) -> loc
  | GSort (loc,_) -> loc
  | GHole (loc,_) -> loc
  | GCast (loc,_,_) -> loc

(**********************************************************************)
(* Conversion from glob_constr to cases pattern, if possible            *)

let rec cases_pattern_of_glob_constr na = function
  | GVar (loc,id) when na<>Anonymous ->
      (* Unable to manage the presence of both an alias and a variable *)
      raise Not_found
  | GVar (loc,id) -> PatVar (loc,Name id)
  | GHole (loc,_) -> PatVar (loc,na)
  | GRef (loc,ConstructRef cstr) ->
      PatCstr (loc,cstr,[],na)
  | GApp (loc,GRef (_,ConstructRef cstr),l) ->
      PatCstr (loc,cstr,List.map (cases_pattern_of_glob_constr Anonymous) l,na)
  | _ -> raise Not_found

(* Turn a closed cases pattern into a glob_constr *)
let rec glob_constr_of_closed_cases_pattern_aux = function
  | PatCstr (loc,cstr,[],Anonymous) ->
      GRef (loc,ConstructRef cstr)
  | PatCstr (loc,cstr,l,Anonymous) ->
      let ref = GRef (loc,ConstructRef cstr) in
      GApp (loc,ref, List.map glob_constr_of_closed_cases_pattern_aux l)
  | _ -> raise Not_found

let glob_constr_of_closed_cases_pattern = function
  | PatCstr (loc,cstr,l,na) ->
      na,glob_constr_of_closed_cases_pattern_aux (PatCstr (loc,cstr,l,Anonymous))
  | _ ->
      raise Not_found

(**********************************************************************)
(* Reduction expressions                                              *)

type 'a glob_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (* true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

let all_flags =
  {rBeta = true; rIota = true; rZeta = true; rDelta = true; rConst = []}

type 'a or_var = ArgArg of 'a | ArgVar of identifier located

type occurrences_expr = bool * int or_var list

let all_occurrences_expr_but l = (false,l)
let no_occurrences_expr_but l = (true,l)
let all_occurrences_expr = (false,[])
let no_occurrences_expr = (true,[])

type 'a with_occurrences = occurrences_expr * 'a

type ('a,'b,'c) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl of 'c with_occurrences option
  | Cbv of 'b glob_red_flag
  | Lazy of 'b glob_red_flag
  | Unfold of 'b with_occurrences list
  | Fold of 'a list
  | Pattern of 'a with_occurrences list
  | ExtraRedExpr of string
  | CbvVm of 'c with_occurrences option

type ('a,'b,'c) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a,'b,'c) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
