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
open Constr
open EConstr
open Names
open Pattern

(* Discrimination nets with bounded depth.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97). *)

let dnet_depth = ref 8

type term_label =
| GRLabel of GlobRef.t
| ProdLabel
| SortLabel

let compare_term_label t1 t2 = match t1, t2 with
| GRLabel gr1, GRLabel gr2 -> GlobRef.CanOrd.compare gr1 gr2
| _ -> pervasives_compare t1 t2 (** OK *)

type 'res lookup_res = 'res Dn.lookup_res = Label of 'res | Nothing | Everything

let eta_reduce = Reductionops.shrink_eta

(* TODO: instead of doing that on patterns we should try to perform it on terms
   before translating them into patterns in Hints. *)
let rec eta_reduce_pat p = match p with
| PLambda (_, _, q) ->
  let f, cl = match eta_reduce_pat q with
  | PApp (f, cl) -> f, cl
  | q -> q, [||]
  in
  let napp = Array.length cl in
  if napp > 0 then
    let r = eta_reduce_pat (Array.last cl) in
    match r with
    | PRel 1 ->
      let lc = Array.sub cl 0 (napp - 1) in
      let u = if Array.is_empty lc then f else PApp (f, lc) in
      if Patternops.noccurn_pattern 1 u then Patternops.lift_pattern (-1) u else p
    | _ -> p
  else p
| PRef _ | PVar _ | PEvar _ | PRel _ | PApp _ | PSoApp _ | PProj _ | PProd _
| PLetIn _ | PSort _ | PMeta _ | PIf _ | PCase _ | PFix _ | PCoFix _ | PInt _
| PFloat _ | PArray _ -> p

let decomp_pat p =
  let rec decrec acc = function
    | PApp (f,args) -> decrec (Array.to_list args @ acc) f
    | PProj (p, c) ->
      let hole = PMeta None in
      let params = List.make (Projection.npars p) hole in
      (PRef (GlobRef.ConstRef (Projection.constant p)), params @ c :: acc)
    | c -> (c,acc)
  in
  decrec [] (eta_reduce_pat p)

let decomp sigma t =
  let rec decrec acc c = match EConstr.kind sigma c with
    | App (f,l) -> decrec (Array.fold_right (fun a l -> a::l) l acc) f
    | Proj (p, c) ->
      (* Hack: fake evar to generate [Everything] in the functions below *)
      let hole = mkEvar (Evar.unsafe_of_int (-1), []) in
      let params = List.make (Projection.npars p) hole in
      (mkConst (Projection.constant p), params @ c :: acc)
    | Cast (c1,_,_) -> decrec acc c1
    | _ -> (c,acc)
  in
    decrec [] (eta_reduce sigma t)

let evaluable_constant c env ts =
  (* This is a hack to work around a broken Print Module implementation, see
     bug #2668. *)
  (if Environ.mem_constant c env then Environ.evaluable_constant c env else true) &&
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_constant ts c)

let evaluable_named id env ts =
  (try Environ.evaluable_named id env with Not_found -> true) &&
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_variable ts id)

(* The pattern view functions below try to overapproximate βι-neutral terms up
   to η-conversion. Some historical design choices are still incorrect w.r.t. to
   this specification. TODO: try to make them follow the spec. *)

let constr_val_discr env sigma ts t =
  (* Should we perform weak βι here? *)
  let c, l = decomp sigma t in
  let open GlobRef in
    match EConstr.kind sigma c with
    | Const (c,u) ->
      if evaluable_constant c env ts then Everything
      else Label(GRLabel (ConstRef c),l)
    | Ind (ind_sp,u) -> Label(GRLabel (IndRef ind_sp),l)
    | Construct (cstr_sp,u) -> Label(GRLabel (ConstructRef cstr_sp),l)
    | Var id ->
      if evaluable_named id env ts then Everything
      else Label(GRLabel (VarRef id),l)
    | Prod (n, d, c) ->
      Label(ProdLabel, [d; c])
    | Lambda (n, d, c) ->
      if Option.is_empty ts && List.is_empty l then Nothing
      else Everything
    | Sort _ -> Label(SortLabel, [])
    | Evar _ -> Everything
    | Case (_, _, _, _, _, c, _) ->
      (* Overapproximate wildly. TODO: be less brutal. *)
      Everything
    | Rel _ | Meta _ | Cast _ | LetIn _ | App _ | Fix _ | CoFix _
    | Proj _ | Int _ | Float _ | Array _ -> Nothing

let constr_pat_discr env ts t =
  let open GlobRef in
  match decomp_pat t with
  | PRef ((IndRef _) as ref), args
  | PRef ((ConstructRef _ ) as ref), args -> Some (GRLabel ref,args)
  | PRef ((VarRef v) as ref), args ->
    if evaluable_named v env ts then None
    else Some(GRLabel ref,args)
  | PRef ((ConstRef c) as ref), args ->
    if evaluable_constant c env ts then None
    else Some (GRLabel ref, args)
  | PVar v, args ->
    if evaluable_named v env ts then None
    else Some(GRLabel (VarRef v),args)
  | PProd (_, d, c), [] ->
    Some (ProdLabel, [d ; c])
  | PLambda (_, d, c), [] -> None
  | PSort s, [] ->
    Some (SortLabel, [])
  | _ -> None

let bounded_constr_pat_discr env st (t,depth) =
  if Int.equal depth 0 then None
  else match constr_pat_discr env st t with
  | None -> None
  | Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

let bounded_constr_val_discr env st sigma (t,depth) =
  if Int.equal depth 0 then
    Nothing
  else match constr_val_discr env sigma st t with
  | Label (c,l) -> Label(c,List.map (fun c -> (c,depth-1)) l)
  | Nothing -> Nothing
  | Everything -> Everything

module Make =
  functor (Z : Map.OrderedType) ->
struct

 module Y = struct
    type t = term_label
    let compare = compare_term_label
 end

 module Dn = Dn.Make(Y)(Z)

 type t = Dn.t

  type pattern = Dn.pattern

  let pattern env st pat =
    Dn.pattern (bounded_constr_pat_discr env st) (pat, !dnet_depth)

  let empty = Dn.empty
  let add = Dn.add
  let rmv = Dn.rmv

  let lookup env sigma st dn t =
    Dn.lookup dn (bounded_constr_val_discr env st sigma) (t,!dnet_depth)

end
