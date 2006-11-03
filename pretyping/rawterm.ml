(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
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

type rawsort = RProp of Term.contents | RType of Univ.universe option

type binder_kind = BProd | BLambda | BLetIn

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (loc * quantified_hypothesis * 'a) list

type 'a bindings = 
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings

type cast_type =
  | CastConv of cast_kind
  | CastCoerce (* Cast to a base type (eg, an underlying inductive type) *)

type rawconstr = 
  | RRef of (loc * global_reference)
  | RVar of (loc * identifier)
  | REvar of loc * existential_key * rawconstr list option
  | RPatVar of loc * (bool * patvar) (* Used for patterns only *)
  | RApp of loc * rawconstr * rawconstr list
  | RLambda of loc * name * rawconstr * rawconstr
  | RProd of loc * name * rawconstr * rawconstr
  | RLetIn of loc * name * rawconstr * rawconstr
  | RCases of loc * rawconstr option * tomatch_tuple * cases_clauses
  | RLetTuple of loc * name list * (name * rawconstr option) * 
      rawconstr * rawconstr
  | RIf of loc * rawconstr * (name * rawconstr option) * rawconstr * rawconstr
  | RRec of loc * fix_kind * identifier array * rawdecl list array *
      rawconstr array * rawconstr array
  | RSort of loc * rawsort
  | RHole of (loc * hole_kind)
  | RCast of loc * rawconstr * cast_type * rawconstr
  | RDynamic of loc * Dyn.t

and rawdecl = name * rawconstr option * rawconstr

and fix_recursion_order = RStructRec | RWfRec of rawconstr | RMeasureRec of rawconstr

and fix_kind =
  | RFix of ((int option * fix_recursion_order) array * int)
  | RCoFix of int

and predicate_pattern =
    name * (loc * inductive * int * name list) option

and tomatch_tuple = (rawconstr * predicate_pattern) list

and cases_clauses =
    (loc * identifier list * cases_pattern list * rawconstr) list

let cases_predicate_names tml =
  List.flatten (List.map (function
    | (tm,(na,None)) -> [na]
    | (tm,(na,Some (_,_,_,nal))) -> na::nal) tml)

(*i - if PRec (_, names, arities, bodies) is in env then arities are
   typed in env too and bodies are typed in env enriched by the
   arities incrementally lifted 

  [On pourrait plutot mettre les arit�s aves le type qu'elles auront
   dans le contexte servant � typer les body ???]

   - boolean in POldCase means it is recursive
i*)
let map_rawdecl f (na,obd,ty) = (na,option_map f obd,f ty)

let map_rawconstr f = function
  | RVar (loc,id) -> RVar (loc,id)
  | RApp (loc,g,args) -> RApp (loc,f g, List.map f args)
  | RLambda (loc,na,ty,c) -> RLambda (loc,na,f ty,f c)
  | RProd (loc,na,ty,c) -> RProd (loc,na,f ty,f c)
  | RLetIn (loc,na,b,c) -> RLetIn (loc,na,f b,f c)
  | RCases (loc,rtntypopt,tml,pl) ->
      RCases (loc,option_map f rtntypopt,
        List.map (fun (tm,x) -> (f tm,x)) tml,
        List.map (fun (loc,idl,p,c) -> (loc,idl,p,f c)) pl)
  | RLetTuple (loc,nal,(na,po),b,c) ->
      RLetTuple (loc,nal,(na,option_map f po),f b,f c)
  | RIf (loc,c,(na,po),b1,b2) ->
      RIf (loc,f c,(na,option_map f po),f b1,f b2)
  | RRec (loc,fk,idl,bl,tyl,bv) ->
      RRec (loc,fk,idl,Array.map (List.map (map_rawdecl f)) bl,
            Array.map f tyl,Array.map f bv)
  | RCast (loc,c,k,t) -> RCast (loc,f c,k,f t)
  | (RSort _ | RHole _ | RRef _ | REvar _ | RPatVar _ | RDynamic _) as x -> x
  

(*
let name_app f e = function
  | Name id -> let (id, e) = f id e in (Name id, e)
  | Anonymous -> Anonymous, e

let fold_ident g idl e =
  let (idl,e) =
    Array.fold_right
      (fun id (idl,e) -> let id,e = g id e in (id::idl,e)) idl ([],e)
  in (Array.of_list idl,e)

let map_rawconstr_with_binders_loc loc g f e = function
  | RVar (_,id) -> RVar (loc,id)
  | RApp (_,a,args) -> RApp (loc,f e a, List.map (f e) args)
  | RLambda (_,na,ty,c) ->
      let na,e = name_app g e na in RLambda (loc,na,f e ty,f e c)
  | RProd (_,na,ty,c) ->
      let na,e = name_app g e na in RProd (loc,na,f e ty,f e c)
  | RLetIn (_,na,b,c) ->
      let na,e = name_app g e na in RLetIn (loc,na,f e b,f e c)
  | RCases (_,tyopt,tml,pl) ->
      (* We don't modify pattern variable since we don't traverse patterns *)
      let g' id e = snd (g id e) in
      let h (_,idl,p,c) = (loc,idl,p,f (List.fold_right g' idl e) c) in
      RCases
	(loc,option_map (f e) tyopt,List.map (f e) tml, List.map h pl)
  | RRec (_,fk,idl,tyl,bv) ->
      let idl',e' = fold_ident g idl e in
      RRec (loc,fk,idl',Array.map (f e) tyl,Array.map (f e') bv)
  | RCast (_,c,t) -> RCast (loc,f e c,f e t)
  | RSort (_,x) -> RSort (loc,x)
  | RHole (_,x)  -> RHole (loc,x)
  | RRef (_,x) -> RRef (loc,x)
  | REvar (_,x,l) -> REvar (loc,x,l)
  | RPatVar (_,x) -> RPatVar (loc,x)
  | RDynamic (_,x) -> RDynamic (loc,x)
*)

let occur_rawconstr id =
  let rec occur = function
    | RVar (loc,id') -> id = id'
    | RApp (loc,f,args) -> (occur f) or (List.exists occur args)
    | RLambda (loc,na,ty,c) -> (occur ty) or ((na <> Name id) & (occur c))
    | RProd (loc,na,ty,c) -> (occur ty) or ((na <> Name id) & (occur c))
    | RLetIn (loc,na,b,c) -> (occur b) or ((na <> Name id) & (occur c))
    | RCases (loc,rtntypopt,tml,pl) ->
	(occur_option rtntypopt)
        or (List.exists (fun (tm,_) -> occur tm) tml)
	or (List.exists occur_pattern pl)
    | RLetTuple (loc,nal,rtntyp,b,c) -> 
	occur_return_type rtntyp id
        or (occur b) or (not (List.mem (Name id) nal) & (occur c))
    | RIf (loc,c,rtntyp,b1,b2) -> 
	occur_return_type rtntyp id or (occur c) or (occur b1) or (occur b2)
    | RRec (loc,fk,idl,bl,tyl,bv) ->
        not (array_for_all4 (fun fid bl ty bd ->
          let rec occur_fix = function
              [] -> not (occur ty) && (fid=id or not(occur bd))
            | (na,bbd,bty)::bl ->
                not (occur bty) &&
                (match bbd with
                    Some bd -> not (occur bd)
                  | _ -> true) &&
                (na=Name id or not(occur_fix bl)) in
          occur_fix bl)
          idl bl tyl bv)
    | RCast (loc,c,_,t) -> (occur c) or (occur t)
    | (RSort _ | RHole _ | RRef _ | REvar _ | RPatVar _ | RDynamic _) -> false

  and occur_pattern (loc,idl,p,c) = not (List.mem id idl) & (occur c)

  and occur_option = function None -> false | Some p -> occur p

  and occur_return_type (na,tyopt) id = na <> Name id & occur_option tyopt

  in occur

let loc_of_rawconstr = function
  | RRef (loc,_) -> loc
  | RVar (loc,_) -> loc
  | REvar (loc,_,_) -> loc
  | RPatVar (loc,_) -> loc
  | RApp (loc,_,_) -> loc
  | RLambda (loc,_,_,_) -> loc
  | RProd (loc,_,_,_) -> loc
  | RLetIn (loc,_,_,_) -> loc
  | RCases (loc,_,_,_) -> loc
  | RLetTuple (loc,_,_,_,_) -> loc
  | RIf (loc,_,_,_,_) -> loc
  | RRec (loc,_,_,_,_,_) -> loc
  | RSort (loc,_) -> loc
  | RHole (loc,_) -> loc
  | RCast (loc,_,_,_) -> loc
  | RDynamic (loc,_) -> loc

(**********************************************************************)
(* Conversion from rawconstr to cases pattern, if possible            *)

let rec cases_pattern_of_rawconstr na = function
  | RVar (loc,id) when na<>Anonymous ->
      (* Unable to manage the presence of both an alias and a variable *)
      raise Not_found
  | RVar (loc,id) -> PatVar (loc,Name id)
  | RHole (loc,_) -> PatVar (loc,na)
  | RRef (loc,ConstructRef cstr) ->
      PatCstr (loc,cstr,[],na)
  | RApp (loc,RRef (_,ConstructRef cstr),l) ->
      PatCstr (loc,cstr,List.map (cases_pattern_of_rawconstr Anonymous) l,na)
  | _ -> raise Not_found

(* Turn a closed cases pattern into a rawconstr *)
let rec rawconstr_of_closed_cases_pattern_aux = function
  | PatCstr (loc,cstr,[],Anonymous) ->
      RRef (loc,ConstructRef cstr)
  | PatCstr (loc,cstr,l,Anonymous) ->
      let ref = RRef (loc,ConstructRef cstr) in
      RApp (loc,ref, List.map rawconstr_of_closed_cases_pattern_aux l)
  | _ -> raise Not_found

let rawconstr_of_closed_cases_pattern = function
  | PatCstr (loc,cstr,l,na) ->
      na,rawconstr_of_closed_cases_pattern_aux (PatCstr (loc,cstr,l,Anonymous))
  | _ ->
      raise Not_found

(**********************************************************************)
(* Reduction expressions                                              *)

type 'a raw_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (* true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

let all_flags =
  {rBeta = true; rIota = true; rZeta = true; rDelta = true; rConst = []}

type 'a or_var = ArgArg of 'a | ArgVar of identifier located

type 'a with_occurrences = int or_var list * 'a

type ('a,'b) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl of 'a with_occurrences option
  | Cbv of 'b raw_red_flag
  | Lazy of 'b raw_red_flag
  | Unfold of 'b with_occurrences list
  | Fold of 'a list
  | Pattern of 'a with_occurrences list
  | ExtraRedExpr of string
  | CbvVm

type ('a,'b) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a,'b) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
