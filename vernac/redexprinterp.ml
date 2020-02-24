(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Names
open CErrors
open Environ
open Evd
open Tacred
open Locus
open CAst
open Libnames
open Genredexpr
open Context.Named.Declaration
open EConstr
open Geninterp
open Constrmetainterp
open Patternops

module type RedExprCoercionSig =
sig
  module N : ConstrCoercionSig
  val coerce_to_evaluable_ref : env -> evar_map -> Val.t -> evaluable_global_reference
  val coerce_to_closed_constr : env -> Val.t -> constr
  val coerce_to_int_or_var_list : Val.t -> int Locus.or_var list
  val coerce_to_int : Val.t -> int
end

module Make (M : RedExprCoercionSig) =
struct

  module F = Constrmetainterp.Make(M.N)

  let try_interp_evaluable env (loc, id) =
    let v = Environ.lookup_named id env in
    match v with
    | LocalDef _ -> EvalVarRef id
    | _ -> error_not_evaluable (GlobRef.VarRef id)

  let interp_evaluable_ref ist env sigma lid =
    try_interp_metalanguage_var M.N.name
      (M.coerce_to_evaluable_ref env sigma) ist (Some (env,sigma)) lid

  let interp_evaluable ist env sigma = function
    | ArgArg (r,Some {loc;v=id}) ->
      (* Maybe [id] has been introduced by Intro-like tactics *)
      begin
        try try_interp_evaluable env (loc, id)
        with Not_found ->
          match r with
          | EvalConstRef _ -> r
          | _ -> Nametab.error_global_not_found (qualid_of_ident ?loc id)
      end
    | ArgArg (r,None) -> r
    | ArgVar {loc;v=id} ->
      try interp_evaluable_ref ist env sigma (CAst.make ?loc id)
      with Not_found ->
        try try_interp_evaluable env (loc, id)
        with Not_found -> Nametab.error_global_not_found (qualid_of_ident ?loc id)

  let interp_int ist ({loc;v=id} as locid) =
    try try_interp_metalanguage_var M.N.name M.coerce_to_int ist None locid
    with Not_found ->
      user_err ?loc ~hdr:"interp_int"
       (str "Unbound variable "  ++ Id.print id ++ str".")

  let interp_int_or_var ist = function
    | ArgVar locid -> interp_int ist locid
    | ArgArg n -> n

  let interp_int_or_var_as_list ist = function
    | ArgVar ({v=id} as locid) ->
        (try M.coerce_to_int_or_var_list (Id.Map.find id ist.lfun)
         with Not_found | CannotCoerceTo _ -> [ArgArg (interp_int ist locid)])
    | ArgArg n as x -> [x]

  let interp_int_or_var_list ist l =
    List.flatten (List.map (interp_int_or_var_as_list ist) l)

  let interp_occurrences ist occs =
    Locusops.occurrences_map (interp_int_or_var_list ist) occs

  (* Interprets a reduction expression *)
  let interp_unfold ist env sigma (occs,qid) =
    (interp_occurrences ist occs,interp_evaluable ist env sigma qid)

  let interp_flag ist env sigma red =
    { red with rConst = List.map (interp_evaluable ist env sigma) red.rConst }

  let interp_constr_with_occurrences ist env sigma (occs,c) =
    let (sigma,c_interp) = F.interp_constr ist env sigma c in
    sigma , (interp_occurrences ist occs, c_interp)

  let interp_closed_typed_pattern_with_occurrences ist env sigma (occs, a) =
    let p = match a with
    | Inl (ArgVar {loc;v=id}) ->
        (* This is the encoding of an ltac var supposed to be bound
           prioritary to an evaluable reference and otherwise to a constr
           (it is an encoding to satisfy the "union" type given to Simpl) *)
      let coerce_eval_ref_or_constr x =
        try Inl (M.coerce_to_evaluable_ref env sigma x)
        with CannotCoerceTo _ ->
          let c = M.coerce_to_closed_constr env x in
          Inr (pattern_of_constr env sigma (EConstr.to_constr sigma c)) in
      (try try_interp_metalanguage_var M.N.name
             coerce_eval_ref_or_constr ist (Some (env,sigma)) (CAst.make ?loc id)
       with Not_found ->
         Nametab.error_global_not_found (qualid_of_ident ?loc id))
    | Inl (ArgArg _ as b) -> Inl (interp_evaluable ist env sigma b)
    | Inr c -> Inr (F.interp_typed_pattern ist env sigma c) in
    interp_occurrences ist occs, p

  let interp_red_expr ist env sigma = function
    | Unfold l -> sigma , Unfold (List.map (interp_unfold ist env sigma) l)
    | Fold l ->
      let (sigma,l_interp) = F.interp_constr_list ist env sigma l in
      sigma , Fold l_interp
    | Cbv flags -> sigma , Cbv (interp_flag ist env sigma flags)
    | Cbn flags -> sigma , Cbn (interp_flag ist env sigma flags)
    | Lazy flags -> sigma , Lazy (interp_flag ist env sigma flags)
    | Pattern l ->
        let (sigma,l_interp) =
          Evd.MonadR.List.map_right
            (fun c sigma -> interp_constr_with_occurrences ist env sigma c) l sigma
        in
        sigma , Pattern l_interp
    | Simpl (flags,o) ->
       sigma , Simpl (interp_flag ist env sigma flags,
                      Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
    | CbvVm o ->
      sigma , CbvVm (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
    | CbvNative o ->
      sigma , CbvNative (Option.map (interp_closed_typed_pattern_with_occurrences ist env sigma) o)
    | (Red _ |  Hnf | ExtraRedExpr _ as r) -> sigma , r

end
