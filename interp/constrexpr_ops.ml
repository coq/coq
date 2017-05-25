(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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
  List.flatten (List.map (function CLocalAssum(l,_,_)->l|_->[]) bl)

let names_of_local_binders bl =
  List.flatten (List.map (function CLocalAssum(l,_,_)->l|CLocalDef(l,_,_)->[l]|CLocalPattern _ -> assert false) bl)

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
  if CAst.(p1.v == p2.v) then true
  else match CAst.(p1.v, p2.v) with
  | CPatAlias(a1,i1), CPatAlias(a2,i2) ->
      Id.equal i1 i2 && cases_pattern_expr_eq a1 a2
  | CPatCstr(c1,a1,b1), CPatCstr(c2,a2,b2) ->
      eq_reference c1 c2 &&
      Option.equal (List.equal cases_pattern_expr_eq) a1 a2 &&
      List.equal cases_pattern_expr_eq b1 b2
  | CPatAtom(r1), CPatAtom(r2) ->
      Option.equal eq_reference r1 r2
  | CPatOr a1, CPatOr a2 ->
      List.equal cases_pattern_expr_eq a1 a2
  | CPatNotation (n1, s1, l1), CPatNotation (n2, s2, l2) ->
    String.equal n1 n2 &&
    cases_pattern_notation_substitution_eq s1 s2 &&
    List.equal cases_pattern_expr_eq l1 l2
  | CPatPrim i1, CPatPrim i2 ->
      prim_token_eq i1 i2
  | CPatRecord l1, CPatRecord l2 ->
      let equal (r1, e1) (r2, e2) =
        eq_reference r1 r2 && cases_pattern_expr_eq e1 e2
      in
      List.equal equal l1 l2
  | CPatDelimiters(s1,e1), CPatDelimiters(s2,e2) ->
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
  if CAst.(e1.v == e2.v) then true
  else match CAst.(e1.v, e2.v) with
  | CRef (r1,u1), CRef (r2,u2) -> eq_reference r1 r2 && eq_universes u1 u2
  | CFix(id1,fl1), CFix(id2,fl2) ->
      eq_located Id.equal id1 id2 &&
      List.equal fix_expr_eq fl1 fl2
  | CCoFix(id1,fl1), CCoFix(id2,fl2) ->
      eq_located Id.equal id1 id2 &&
      List.equal cofix_expr_eq fl1 fl2
  | CProdN(bl1,a1), CProdN(bl2,a2) ->
      List.equal binder_expr_eq bl1 bl2 &&
      constr_expr_eq a1 a2
  | CLambdaN(bl1,a1), CLambdaN(bl2,a2) ->
      List.equal binder_expr_eq bl1 bl2 &&
      constr_expr_eq a1 a2
  | CLetIn((_,na1),a1,t1,b1), CLetIn((_,na2),a2,t2,b2) ->
      Name.equal na1 na2 &&
      constr_expr_eq a1 a2 &&
      Option.equal constr_expr_eq t1 t2 &&
      constr_expr_eq b1 b2
  | CAppExpl((proj1,r1,_),al1), CAppExpl((proj2,r2,_),al2) ->
      Option.equal Int.equal proj1 proj2 &&
      eq_reference r1 r2 &&
      List.equal constr_expr_eq al1 al2
  | CApp((proj1,e1),al1), CApp((proj2,e2),al2) ->
      Option.equal Int.equal proj1 proj2 &&
      constr_expr_eq e1 e2 &&
      List.equal args_eq al1 al2
  | CRecord l1, CRecord l2 ->
    let field_eq (r1, e1) (r2, e2) =
      eq_reference r1 r2 && constr_expr_eq e1 e2
    in
    List.equal field_eq l1 l2
  | CCases(_,r1,a1,brl1), CCases(_,r2,a2,brl2) ->
      (** Don't care about the case_style *)
      Option.equal constr_expr_eq r1 r2 &&
      List.equal case_expr_eq a1 a2 &&
      List.equal branch_expr_eq brl1 brl2
  | CLetTuple (n1, (m1, e1), t1, b1), CLetTuple (n2, (m2, e2), t2, b2) ->
    List.equal (eq_located Name.equal) n1 n2 &&
    Option.equal (eq_located Name.equal) m1 m2 &&
    Option.equal constr_expr_eq e1 e2 &&
    constr_expr_eq t1 t2 &&
    constr_expr_eq b1 b2
  | CIf (e1, (n1, r1), t1, f1), CIf (e2, (n2, r2), t2, f2) ->
    constr_expr_eq e1 e2 &&
    Option.equal (eq_located Name.equal) n1 n2 &&
    Option.equal constr_expr_eq r1 r2 &&
    constr_expr_eq t1 t2 &&
    constr_expr_eq f1 f2
  | CHole _, CHole _ -> true
  | CPatVar i1, CPatVar i2 ->
    Id.equal i1 i2
  | CEvar (id1, c1), CEvar (id2, c2) ->
    Id.equal id1 id2 && List.equal instance_eq c1 c2
  | CSort s1, CSort s2 ->
    Miscops.glob_sort_eq s1 s2
  | CCast(a1,(CastConv b1|CastVM b1)), CCast(a2,(CastConv b2|CastVM b2)) ->
      constr_expr_eq a1 a2 &&
      constr_expr_eq b1 b2
  | CCast(a1,CastCoerce), CCast(a2, CastCoerce) ->
      constr_expr_eq a1 a2
  | CNotation(n1, s1), CNotation(n2, s2) ->
      String.equal n1 n2 &&
      constr_notation_substitution_eq s1 s2
  | CPrim i1, CPrim i2 ->
    prim_token_eq i1 i2
  | CGeneralization (bk1, ak1, e1), CGeneralization (bk2, ak2, e2) ->
    binding_kind_eq bk1 bk2 &&
    Option.equal abstraction_kind_eq ak1 ak2 &&
    constr_expr_eq e1 e2
  | CDelimiters(s1,e1), CDelimiters(s2,e2) ->
    String.equal s1 s2 &&
    constr_expr_eq e1 e2
  | _ -> false

and args_eq (a1,e1) (a2,e2) =
  Option.equal (eq_located explicitation_eq) e1 e2 &&
  constr_expr_eq a1 a2

and case_expr_eq (e1, n1, p1) (e2, n2, p2) =
  constr_expr_eq e1 e2 &&
  Option.equal (eq_located Name.equal) n1 n2 &&
  Option.equal cases_pattern_expr_eq p1 p2

and branch_expr_eq (_, (p1, e1)) (_, (p2, e2)) =
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
| CLocalDef (n1, e1, t1), CLocalDef (n2, e2, t2) ->
  eq_located Name.equal n1 n2 && constr_expr_eq e1 e2 && Option.equal constr_expr_eq t1 t2
| CLocalAssum (n1, _, e1), CLocalAssum (n2, _, e2) ->
  (** Don't care about the [binder_kind] *)
  List.equal (eq_located Name.equal) n1 n2 && constr_expr_eq e1 e2
| _ -> false

and constr_notation_substitution_eq (e1, el1, bl1) (e2, el2, bl2) =
  List.equal constr_expr_eq e1 e2 &&
  List.equal (List.equal constr_expr_eq) el1 el2 &&
  List.equal (List.equal local_binder_eq) bl1 bl2

and instance_eq (x1,c1) (x2,c2) =
  Id.equal x1 x2 && constr_expr_eq c1 c2

let constr_loc c = CAst.(c.loc)
let cases_pattern_expr_loc cp = CAst.(cp.loc)

let local_binder_loc = function
  | CLocalAssum ((loc,_)::_,_,t)
  | CLocalDef ((loc,_),t,None) -> Loc.merge_opt loc (constr_loc t)
  | CLocalDef ((loc,_),b,Some t) -> Loc.merge_opt loc (Loc.merge_opt (constr_loc b) (constr_loc t))
  | CLocalAssum ([],_,_) -> assert false
  | CLocalPattern (loc,_) -> loc

let local_binders_loc bll = match bll with
  | []     -> None
  | h :: l -> Loc.merge_opt (local_binder_loc h) (local_binder_loc (List.last bll))

(** Pseudo-constructors *)

let mkIdentC id   = CAst.make @@ CRef (Ident (Loc.tag id),None)
let mkRefC r      = CAst.make @@ CRef (r,None)
let mkCastC (a,k) = CAst.make @@ CCast (a,k)
let mkLambdaC (idl,bk,a,b) = CAst.make @@ CLambdaN ([idl,bk,a],b)
let mkLetInC  (id,a,t,b)   = CAst.make @@ CLetIn (id,a,t,b)
let mkProdC   (idl,bk,a,b) = CAst.make @@ CProdN ([idl,bk,a],b)

let mkAppC (f,l) =
  let l = List.map (fun x -> (x,None)) l in
  match CAst.(f.v) with
  | CApp (g,l') -> CAst.make @@ CApp (g, l' @ l)
  | _           -> CAst.make @@ CApp ((None, f), l)

let add_name_in_env env n =
  match snd n with
  | Anonymous -> env
  | Name id -> id :: env

let (fresh_var, fresh_var_hook) = Hook.make ~default:(fun _ _ -> assert false) ()

let expand_binders ?loc mkC bl c =
  let rec loop ?loc bl c =
    match bl with
    | [] -> ([], c)
    | b :: bl ->
        match b with
        | CLocalDef ((loc1,_) as n, oty, b) ->
            let env, c = loop ?loc:(Loc.merge_opt loc1 loc) bl c in
            let env = add_name_in_env env n in
            (env, CAst.make ?loc @@ CLetIn (n,oty,b,c))
        | CLocalAssum ((loc1,_)::_ as nl, bk, t) ->
            let env, c = loop ?loc:(Loc.merge_opt loc1 loc) bl c in
            let env = List.fold_left add_name_in_env env nl in
            (env, mkC ?loc (nl,bk,t) c)
        | CLocalAssum ([],_,_) -> loop ?loc bl c
        | CLocalPattern (loc1, (p, ty)) ->
            let env, c = loop ?loc:(Loc.merge_opt loc1 loc) bl c in
            let ni = Hook.get fresh_var env c in
            let id = (loc1, Name ni) in
            let ty = match ty with
                 | Some ty -> ty
                 | None -> CAst.make ?loc:loc1 @@ CHole (None, IntroAnonymous, None)
            in
            let e = CAst.make @@ CRef (Libnames.Ident (loc1, ni), None) in
            let c = CAst.make ?loc @@
              CCases
                (LetPatternStyle, None, [(e,None,None)],
                 [(Loc.tag ?loc:loc1 ([(loc1,[p])], c))])
            in
            (ni :: env, mkC ?loc ([id],Default Explicit,ty) c)
  in
  let (_, c) = loop ?loc bl c in
  c

let mkCProdN ?loc bll c =
  let mk ?loc b c = CAst.make ?loc @@ CProdN ([b],c) in
  expand_binders ?loc mk bll c

let mkCLambdaN ?loc bll c =
  let mk ?loc b c = CAst.make ?loc @@ CLambdaN ([b],c) in
  expand_binders ?loc mk bll c

(* Deprecated *)
let abstract_constr_expr c bl = mkCLambdaN ?loc:(local_binders_loc bl) bl c
let prod_constr_expr c bl =  mkCProdN ?loc:(local_binders_loc bl) bl c

let coerce_reference_to_id = function
  | Ident (_,id) -> id
  | Qualid (loc,_) ->
      CErrors.user_err ?loc ~hdr:"coerce_reference_to_id"
        (str "This expression should be a simple identifier.")

let coerce_to_id = function
  | { CAst.v = CRef (Ident (loc,id),_); _ } -> (loc,id)
  | { CAst.loc; _ } -> CErrors.user_err ?loc
       ~hdr:"coerce_to_id"
         (str "This expression should be a simple identifier.")

let coerce_to_name = function
  | { CAst.v = CRef (Ident (loc,id),_) } -> (loc,Name id)
  | { CAst.loc; CAst.v = CHole (_,_,_) } -> (loc,Anonymous)
  | { CAst.loc; _ } -> CErrors.user_err ?loc ~hdr:"coerce_to_name"
                         (str "This expression should be a name.")
