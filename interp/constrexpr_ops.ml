(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Libnames
open Constrexpr
open Misctypes
open Decl_kinds

(***********************)
(* For binders parsing *)

let binding_kind_eq bk1 bk2 = match bk1, bk2 with
| Explicit, Explicit -> true
| Implicit, Implicit -> true
| _ -> false

let abstraction_kind_eq ak1 ak2 = match ak1, ak2 with
| AbsLambda, AbsLambda -> true
| AbsPi, AbsPi -> true
| _ -> false

let binder_kind_eq b1 b2 = match b1, b2 with
| Default bk1, Default bk2 -> binding_kind_eq bk1 bk2
| Generalized (bk1, ck1, b1), Generalized (bk2, ck2, b2) ->
  binding_kind_eq bk1 bk2 && binding_kind_eq ck1 ck2 &&
  (if b1 then b2 else not b2)
| _ -> false

let default_binder_kind = Default Explicit

let names_of_local_assums bl =
  List.flatten (List.map (function LocalRawAssum(l,_,_)->l|_->[]) bl)

let names_of_local_binders bl =
  List.flatten (List.map (function LocalRawAssum(l,_,_)->l|LocalRawDef(l,_)->[l]) bl)

(**********************************************************************)
(* Functions on constr_expr *)

let prim_token_eq t1 t2 = match t1, t2 with
| Numeral i1, Numeral i2 -> Bigint.equal i1 i2
| String s1, String s2 -> String.equal s1 s2
| _ -> false

let explicitation_eq ex1 ex2 = match ex1, ex2 with
| ExplByPos (i1, id1), ExplByPos (i2, id2) ->
  Int.equal i1 i2 && Option.equal Id.equal id1 id2
| ExplByName id1, ExplByName id2 ->
  Id.equal id1 id2
| _ -> false

let eq_located f (_, x) (_, y) = f x y

let rec cases_pattern_expr_eq p1 p2 =
  if p1 == p2 then true
  else match p1, p2 with
  | CPatAlias(_,a1,i1), CPatAlias(_,a2,i2) ->
      Id.equal i1 i2 && cases_pattern_expr_eq a1 a2
  | CPatCstr(_,c1,a1,b1), CPatCstr(_,c2,a2,b2) ->
      eq_reference c1 c2 &&
      List.equal cases_pattern_expr_eq a1 a2 &&
      List.equal cases_pattern_expr_eq b1 b2
  | CPatAtom(_,r1), CPatAtom(_,r2) ->
      Option.equal eq_reference r1 r2
  | CPatOr (_, a1), CPatOr (_, a2) ->
      List.equal cases_pattern_expr_eq a1 a2
  | CPatNotation (_, n1, s1, l1), CPatNotation (_, n2, s2, l2) ->
    String.equal n1 n2 &&
    cases_pattern_notation_substitution_eq s1 s2 &&
    List.equal cases_pattern_expr_eq l1 l2
  | CPatPrim(_,i1), CPatPrim(_,i2) ->
      prim_token_eq i1 i2
  | CPatRecord (_, l1), CPatRecord (_, l2) ->
      let equal (r1, e1) (r2, e2) =
        eq_reference r1 r2 && cases_pattern_expr_eq e1 e2
      in
      List.equal equal l1 l2
  | CPatDelimiters(_,s1,e1), CPatDelimiters(_,s2,e2) ->
      String.equal s1 s2 && cases_pattern_expr_eq e1 e2
  | _ -> false

and cases_pattern_notation_substitution_eq (s1, n1) (s2, n2) =
  List.equal cases_pattern_expr_eq s1 s2 &&
  List.equal (List.equal cases_pattern_expr_eq) n1 n2

let eq_universes u1 u2 =
  match u1, u2 with
  | None, None -> true
  | Some l, Some l' -> l = l'
  | _, _ -> false

let rec constr_expr_eq e1 e2 =
  if e1 == e2 then true
  else match e1, e2 with
  | CRef (r1,u1), CRef (r2,u2) -> eq_reference r1 r2 && eq_universes u1 u2
  | CFix(_,id1,fl1), CFix(_,id2,fl2) ->
      eq_located Id.equal id1 id2 &&
      List.equal fix_expr_eq fl1 fl2
  | CCoFix(_,id1,fl1), CCoFix(_,id2,fl2) ->
      eq_located Id.equal id1 id2 &&
      List.equal cofix_expr_eq fl1 fl2
  | CProdN(_,bl1,a1), CProdN(_,bl2,a2) ->
      List.equal binder_expr_eq bl1 bl2 &&
      constr_expr_eq a1 a2
  | CLambdaN(_,bl1,a1), CLambdaN(_,bl2,a2) ->
      List.equal binder_expr_eq bl1 bl2 &&
      constr_expr_eq a1 a2
  | CLetIn(_,(_,na1),a1,b1), CLetIn(_,(_,na2),a2,b2) ->
      Name.equal na1 na2 &&
      constr_expr_eq a1 a2 &&
      constr_expr_eq b1 b2
  | CAppExpl(_,(proj1,r1,_),al1), CAppExpl(_,(proj2,r2,_),al2) ->
      Option.equal Int.equal proj1 proj2 &&
      eq_reference r1 r2 &&
      List.equal constr_expr_eq al1 al2
  | CApp(_,(proj1,e1),al1), CApp(_,(proj2,e2),al2) ->
      Option.equal Int.equal proj1 proj2 &&
      constr_expr_eq e1 e2 &&
      List.equal args_eq al1 al2
  | CRecord (_, e1, l1), CRecord (_, e2, l2) ->
    let field_eq (r1, e1) (r2, e2) =
      eq_reference r1 r2 && constr_expr_eq e1 e2
    in
    Option.equal constr_expr_eq e1 e2 &&
    List.equal field_eq l1 l2
  | CCases(_,_,r1,a1,brl1), CCases(_,_,r2,a2,brl2) ->
      (** Don't care about the case_style *)
      Option.equal constr_expr_eq r1 r2 &&
      List.equal case_expr_eq a1 a2 &&
      List.equal branch_expr_eq brl1 brl2
  | CLetTuple (_, n1, (m1, e1), t1, b1), CLetTuple (_, n2, (m2, e2), t2, b2) ->
    List.equal (eq_located Name.equal) n1 n2 &&
    Option.equal (eq_located Name.equal) m1 m2 &&
    Option.equal constr_expr_eq e1 e2 &&
    constr_expr_eq t1 t2 &&
    constr_expr_eq b1 b2
  | CIf (_, e1, (n1, r1), t1, f1), CIf (_, e2, (n2, r2), t2, f2) ->
    constr_expr_eq e1 e2 &&
    Option.equal (eq_located Name.equal) n1 n2 &&
    Option.equal constr_expr_eq r1 r2 &&
    constr_expr_eq t1 t2 &&
    constr_expr_eq f1 f2
  | CHole _, CHole _ -> true
  | CPatVar(_,i1), CPatVar(_,i2) ->
    Id.equal i1 i2
  | CEvar (_, id1, c1), CEvar (_, id2, c2) ->
    Id.equal id1 id2 && List.equal instance_eq c1 c2
  | CSort(_,s1), CSort(_,s2) ->
    Miscops.glob_sort_eq s1 s2
  | CCast(_,a1,(CastConv b1|CastVM b1)), CCast(_,a2,(CastConv b2|CastVM b2)) ->
      constr_expr_eq a1 a2 &&
      constr_expr_eq b1 b2
  | CCast(_,a1,CastCoerce), CCast(_,a2, CastCoerce) ->
      constr_expr_eq a1 a2
  | CNotation(_, n1, s1), CNotation(_, n2, s2) ->
      String.equal n1 n2 &&
      constr_notation_substitution_eq s1 s2
  | CPrim(_,i1), CPrim(_,i2) ->
    prim_token_eq i1 i2
  | CGeneralization (_, bk1, ak1, e1), CGeneralization (_, bk2, ak2, e2) ->
    binding_kind_eq bk1 bk2 &&
    Option.equal abstraction_kind_eq ak1 ak2 &&
    constr_expr_eq e1 e2
  | CDelimiters(_,s1,e1), CDelimiters(_,s2,e2) ->
    String.equal s1 s2 &&
    constr_expr_eq e1 e2
  | _ -> false

and args_eq (a1,e1) (a2,e2) =
  Option.equal (eq_located explicitation_eq) e1 e2 &&
  constr_expr_eq a1 a2

and case_expr_eq (e1, (n1, p1)) (e2, (n2, p2)) =
  constr_expr_eq e1 e2 &&
  Option.equal (eq_located Name.equal) n1 n2 &&
  Option.equal cases_pattern_expr_eq p1 p2

and branch_expr_eq (_, p1, e1) (_, p2, e2) =
  List.equal (eq_located (List.equal cases_pattern_expr_eq)) p1 p2 &&
  constr_expr_eq e1 e2

and binder_expr_eq ((n1, _, e1) : binder_expr) (n2, _, e2) =
  (** Don't care about the [binder_kind] *)
  List.equal (eq_located Name.equal) n1 n2 && constr_expr_eq e1 e2

and fix_expr_eq (id1,(j1, r1),bl1,a1,b1) (id2,(j2, r2),bl2,a2,b2) =
  (eq_located Id.equal id1 id2) &&
  Option.equal (eq_located Id.equal) j1 j2 &&
  recursion_order_expr_eq r1 r2 &&
  List.equal local_binder_eq bl1 bl2 &&
  constr_expr_eq a1 a2 &&
  constr_expr_eq b1 b2

and cofix_expr_eq (id1,bl1,a1,b1) (id2,bl2,a2,b2) =
  (eq_located Id.equal id1 id2) &&
  List.equal local_binder_eq bl1 bl2 &&
  constr_expr_eq a1 a2 &&
  constr_expr_eq b1 b2

and recursion_order_expr_eq r1 r2 = match r1, r2 with
| CStructRec, CStructRec -> true
| CWfRec e1, CWfRec e2 -> constr_expr_eq e1 e2
| CMeasureRec (e1, o1), CMeasureRec (e2, o2) ->
  constr_expr_eq e1 e2 && Option.equal constr_expr_eq o1 o2
| _ -> false

and local_binder_eq l1 l2 = match l1, l2 with
| LocalRawDef (n1, e1), LocalRawDef (n2, e2) ->
  eq_located Name.equal n1 n2 && constr_expr_eq e1 e2
| LocalRawAssum (n1, _, e1), LocalRawAssum (n2, _, e2) ->
  (** Don't care about the [binder_kind] *)
  List.equal (eq_located Name.equal) n1 n2 && constr_expr_eq e1 e2
| _ -> false

and constr_notation_substitution_eq (e1, el1, bl1) (e2, el2, bl2) =
  List.equal constr_expr_eq e1 e2 &&
  List.equal (List.equal constr_expr_eq) el1 el2 &&
  List.equal (List.equal local_binder_eq) bl1 bl2

and instance_eq (x1,c1) (x2,c2) =
  Id.equal x1 x2 && constr_expr_eq c1 c2

let constr_loc = function
  | CRef (Ident (loc,_),_) -> loc
  | CRef (Qualid (loc,_),_) -> loc
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
  | CHole (loc,_,_,_) -> loc
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

let mkIdentC id  = CRef (Ident (Loc.ghost, id),None)
let mkRefC r     = CRef (r,None)
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
  | CRef (Ident (loc,id),_) -> (loc,id)
  | a -> Errors.user_err_loc
        (constr_loc a,"coerce_to_id",
         str "This expression should be a simple identifier.")

let coerce_to_name = function
  | CRef (Ident (loc,id),_) -> (loc,Name id)
  | CHole (loc,_,_,_) -> (loc,Anonymous)
  | a -> Errors.user_err_loc
        (constr_loc a,"coerce_to_name",
         str "This expression should be a name.")
