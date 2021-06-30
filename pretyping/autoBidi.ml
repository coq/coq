(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Constr
open EConstr
open Reduction

let rigid_heads env c1 c2 =
  let open Names.GlobRef in
  if QGlobRef.equal env c1 c2 then
    match c1 with
    | VarRef id -> Context.Named.Declaration.is_local_assum (lookup_named id env)
    | ConstRef c ->
      let open Declarations in
      begin match (lookup_constant c env).const_body with
        | Undef _ | OpaqueDef _ -> true
        | Def _ | Primitive _ -> false
      end
    | IndRef _ | ConstructRef _ -> true
  else false

let rigid_heads env sigma c1 c2 =
  match destRef sigma c1, destRef sigma c2 with
  | exception DestKO -> false
  | (c1,_), (c2,_) -> rigid_heads env c1 c2

(* NB: we don't use the rel_context *)
(* If [coercible] the type constraint may be satisfied by a coercion
   instead of unification, so don't use bidi.
   Typically [fun x : sigT (fun _ : supertype => _) => projT1 x : subtype].
 *)
let rec match_rigidly env sigma candargs ~coercible pb k ty tycon =
  match kind_nocast_gen (kind sigma) ty, kind_nocast_gen (kind sigma) tycon with
  | Cast _, _ | _, Cast _ -> assert false
  | Rel n1, _ ->
    if not coercible
    && n1 > k && n1 - k <= Array.length candargs
    && EConstr.Vars.noccur_between sigma 1 k tycon
    then candargs.(n1 - k - 1) <- Some (pb, EConstr.Vars.lift (-k) tycon)
    else ()

  | Meta _, Meta _
  | Var _, Var _
  | Int _, Int _
  | Float _, Float _
  | Sort _, Sort _ -> ()

  | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
    match_rigidly env sigma candargs ~coercible:false CONV k t1 t2;
    match_rigidly env sigma candargs ~coercible:false CONV (k+1) c1 c2

  | Prod (_,t1,c1), Prod (_,t2,c2) ->
    match_rigidly env sigma candargs ~coercible CONV k t1 t2;
    match_rigidly env sigma candargs ~coercible pb (k+1) c1 c2

  | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) -> ()

  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    if rigid_heads env sigma c1 c2 && Int.equal len (Array.length l2) then begin
      Array.iter2 (match_rigidly env sigma candargs ~coercible:false CONV k) l1 l2
    end

  | Proj (p1,c1), Proj (p2,c2) -> ()

  | Evar (e1,l1), Evar (e2,l2) -> ()

  | Const _, Const _
  | Ind _, Ind _
  | Construct _, Construct _ ->
    ()

  | Case (ci1,u1,pms1,p1,iv1,c1,bl1), Case (ci2,u2,pms2,p2,iv2,c2,bl2) -> ()

  | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) -> ()

  | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) -> ()

  | Array(u1,t1,def1,ty1), Array(u2,t2,def2,ty2) ->
    if Array.length t1 = Array.length t2 then begin
      match_rigidly env sigma candargs ~coercible:false CONV k ty1 ty2;
      Array.iter2 (match_rigidly env sigma candargs ~coercible:false CONV k) t1 t2;
      match_rigidly env sigma candargs ~coercible:false CONV k def1 def2
    end

  | (Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _| Array _), _ -> ()

let auto_bidi env sigma hj ~nargs tycon =
  let ty = hj.uj_type in
  match decompose_prod_n_assum sigma nargs ty with
  | exception CErrors.UserError _ -> []
  | ctx, ty ->
    (* TODO handle letins *)
    if List.exists Context.Rel.Declaration.is_local_def ctx then []
    else
      let candargs = Array.make nargs None in
      match_rigidly env sigma candargs ~coercible:true CUMUL 0 ty tycon;
      let candargs = CArray.rev_to_list candargs in
      candargs

let should_auto_bidi = Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Automatic";"Bidirectionality"] ~value:true

let auto_bidi env sigma hj ~nargs tycon =
  if should_auto_bidi () then auto_bidi env sigma hj ~nargs tycon
  else []
