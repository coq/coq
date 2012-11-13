(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Libnames
open Glob_term
open Constrexpr
open Decl_kinds

(***********************)
(* For binders parsing *)

let default_binder_kind = Default Explicit

let names_of_local_assums bl =
  List.flatten (List.map (function LocalRawAssum(l,_,_)->l|_->[]) bl)

let names_of_local_binders bl =
  List.flatten (List.map (function LocalRawAssum(l,_,_)->l|LocalRawDef(l,_)->[l]) bl)

(**********************************************************************)
(* Functions on constr_expr *)

let constr_loc = function
  | CRef (Ident (loc,_)) -> loc
  | CRef (Qualid (loc,_)) -> loc
  | CFix (loc,_,_) -> loc
  | CCoFix (loc,_,_) -> loc
  | CProdN (loc,_,_) -> loc
  | CLambdaN (loc,_,_) -> loc
  | CLetIn (loc,_,_,_) -> loc
  | CAppExpl (loc,_,_) -> loc
  | CApp (loc,_,_) -> loc
  | CRecord (loc,_,_) -> loc
  | CCases (loc,_,_,_,_) -> loc
  | CLetTuple (loc,_,_,_,_) -> loc
  | CIf (loc,_,_,_,_) -> loc
  | CHole (loc, _) -> loc
  | CPatVar (loc,_) -> loc
  | CEvar (loc,_,_) -> loc
  | CSort (loc,_) -> loc
  | CCast (loc,_,_) -> loc
  | CNotation (loc,_,_) -> loc
  | CGeneralization (loc,_,_,_) -> loc
  | CPrim (loc,_) -> loc
  | CDelimiters (loc,_,_) -> loc

let cases_pattern_expr_loc = function
  | CPatAlias (loc,_,_) -> loc
  | CPatCstr (loc,_,_,_) -> loc
  | CPatAtom (loc,_) -> loc
  | CPatOr (loc,_) -> loc
  | CPatNotation (loc,_,_,_) -> loc
  | CPatRecord (loc, _) -> loc
  | CPatPrim (loc,_) -> loc
  | CPatDelimiters (loc,_,_) -> loc

let raw_cases_pattern_expr_loc = function
  | RCPatAlias (loc,_,_) -> loc
  | RCPatCstr (loc,_,_,_) -> loc
  | RCPatAtom (loc,_) -> loc
  | RCPatOr (loc,_) -> loc

let local_binder_loc = function
  | LocalRawAssum ((loc,_)::_,_,t)
  | LocalRawDef ((loc,_),t) -> Loc.merge loc (constr_loc t)
  | LocalRawAssum ([],_,_) -> assert false

let local_binders_loc bll = match bll with
  | [] -> Loc.ghost
  | h :: l ->
    Loc.merge (local_binder_loc h) (local_binder_loc (List.last bll))

(** Pseudo-constructors *)

let mkIdentC id  = CRef (Ident (Loc.ghost, id))
let mkRefC r     = CRef r
let mkCastC (a,k)  = CCast (Loc.ghost,a,k)
let mkLambdaC (idl,bk,a,b) = CLambdaN (Loc.ghost,[idl,bk,a],b)
let mkLetInC (id,a,b)   = CLetIn (Loc.ghost,id,a,b)
let mkProdC (idl,bk,a,b)   = CProdN (Loc.ghost,[idl,bk,a],b)

let mkAppC (f,l) =
  let l = List.map (fun x -> (x,None)) l in
  match f with
  | CApp (_,g,l') -> CApp (Loc.ghost, g, l' @ l)
  | _ -> CApp (Loc.ghost, (None, f), l)

let rec mkCProdN loc bll c =
  match bll with
  | LocalRawAssum ((loc1,_)::_ as idl,bk,t) :: bll ->
      CProdN (loc,[idl,bk,t],mkCProdN (Loc.merge loc1 loc) bll c)
  | LocalRawDef ((loc1,_) as id,b) :: bll ->
      CLetIn (loc,id,b,mkCProdN (Loc.merge loc1 loc) bll c)
  | [] -> c
  | LocalRawAssum ([],_,_) :: bll -> mkCProdN loc bll c

let rec mkCLambdaN loc bll c =
  match bll with
  | LocalRawAssum ((loc1,_)::_ as idl,bk,t) :: bll ->
      CLambdaN (loc,[idl,bk,t],mkCLambdaN (Loc.merge loc1 loc) bll c)
  | LocalRawDef ((loc1,_) as id,b) :: bll ->
      CLetIn (loc,id,b,mkCLambdaN (Loc.merge loc1 loc) bll c)
  | [] -> c
  | LocalRawAssum ([],_,_) :: bll -> mkCLambdaN loc bll c

let rec abstract_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,abstract_constr_expr c bl)
  | LocalRawAssum (idl,bk,t)::bl ->
      List.fold_right (fun x b -> mkLambdaC([x],bk,t,b)) idl
      (abstract_constr_expr c bl)

let rec prod_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,prod_constr_expr c bl)
  | LocalRawAssum (idl,bk,t)::bl ->
      List.fold_right (fun x b -> mkProdC([x],bk,t,b)) idl
      (prod_constr_expr c bl)

let coerce_reference_to_id = function
  | Ident (_,id) -> id
  | Qualid (loc,_) ->
      Errors.user_err_loc (loc, "coerce_reference_to_id",
        str "This expression should be a simple identifier.")

let coerce_to_id = function
  | CRef (Ident (loc,id)) -> (loc,id)
  | a -> Errors.user_err_loc
        (constr_loc a,"coerce_to_id",
         str "This expression should be a simple identifier.")

let coerce_to_name = function
  | CRef (Ident (loc,id)) -> (loc,Name id)
  | CHole (loc,_) -> (loc,Anonymous)
  | a -> Errors.user_err_loc
        (constr_loc a,"coerce_to_name",
         str "This expression should be a name.")

let rec raw_cases_pattern_expr_of_glob_constr looked_for = function
  | GVar (loc,id) -> RCPatAtom (loc,Some id)
  | GHole (loc,_) -> RCPatAtom (loc,None)
  | GRef (loc,g) ->
    looked_for g;
    RCPatCstr (loc, g,[],[])
  | GApp (loc,GRef (_,g),l) ->
    looked_for g;
    RCPatCstr (loc, g,[],List.map (raw_cases_pattern_expr_of_glob_constr looked_for) l)
  | _ -> raise Not_found
