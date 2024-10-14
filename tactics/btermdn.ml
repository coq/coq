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
open Constr
open Names
open Pattern

(* Discrimination nets with bounded depth.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97). *)

let dnet_depth = ref 8

type term_label =
| GRLabel of GlobRef.t
| ProjLabel of Projection.Repr.t * int
 (** [ProjLabel (p, n)] represents a possibly partially applied projection [p]
     with [n] arguments missing to be fully applied. [n] is always zero for
     labels derived from [Proj] terms but can be greater than zero for labels
     derived from compatibility constants. *)
| ProdLabel
| SortLabel
| CaseLabel

let compare_term_label t1 t2 = match t1, t2 with
| GRLabel gr1, GRLabel gr2 -> GlobRef.UserOrd.compare gr1 gr2
| ProjLabel (p1, n1), ProjLabel (p2, n2) ->
  let c = Int.compare n1 n2 in
  if c <> 0 then c else
    (Projection.Repr.UserOrd.compare p1 p2)
| _ -> Stdlib.compare t1 t2 (** OK *)

type 'res lookup_res = 'res Dn.lookup_res = Label of 'res | Nothing | Everything

let eta_reduce = Reductionops.shrink_eta

(* TODO: instead of doing that on patterns we should try to perform it on terms
   before translating them into patterns in Hints. *)
let rec eta_reduce_pat (p:constr_pattern) = match p with
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
| PFloat _ | PString _ | PArray _ -> p
| PUninstantiated _ -> .

let evaluable_constant c env ts =
  (* This is a hack to work around a broken Print Module implementation, see
     bug #2668. *)
  (if Environ.mem_constant c env then Environ.evaluable_constant c env else true) &&
  (match ts with None -> true | Some ts -> Structures.PrimitiveProjections.is_transparent_constant ts c)

let evaluable_named id env ts =
  (try Environ.evaluable_named id env with Not_found -> true) &&
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_variable ts id)

let evaluable_projection p _env ts =
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_projection ts (Projection.repr p))

let label_of_opaque_constant c stack =
  match Structures.PrimitiveProjections.find_opt c with
  | None -> (GRLabel (ConstRef c), stack)
  | Some p ->
    let n_args_needed = Structures.Structure.projection_nparams c + 1 in (* +1 for the record value itself *)
    let n_args_given = List.length stack in
    let n_args_missing = max (n_args_needed - n_args_given) 0 in
    let n_args_drop = min (n_args_needed - 1) n_args_given in (* we do not drop the record value from the stack *)
    (ProjLabel (p, n_args_missing), List.skipn n_args_drop stack)

(* The pattern view functions below try to overapproximate βι-neutral terms up
   to η-conversion. Some historical design choices are still incorrect w.r.t. to
   this specification. TODO: try to make them follow the spec. *)

let constr_val_discr env sigma ts t =
  (* Should we perform weak βι here? *)
  let open GlobRef in
  let rec decomp stack t =
    match EConstr.kind sigma t with
    | App (f,l) -> decomp (Array.fold_right (fun a l -> a::l) l stack) f
    | Proj (p,_,c) when evaluable_projection p env ts -> Everything
    | Proj (p,_,c) -> Label(ProjLabel (Projection.repr p, 0), c :: stack)
    | Cast (c,_,_) -> decomp stack c
    | Const (c,_) when evaluable_constant c env ts -> Everything
    | Const (c,_) ->
      let c = Environ.QConstant.canonize env c in
      Label (label_of_opaque_constant c stack)
    | Ind (ind_sp,_) ->
      let ind_sp = Environ.QInd.canonize env ind_sp in
      Label(GRLabel (IndRef ind_sp), stack)
    | Construct (cstr_sp,_) ->
      let cstr_sp = Environ.QConstruct.canonize env cstr_sp in
      Label(GRLabel (ConstructRef cstr_sp), stack)
    | Var id when evaluable_named id env ts -> Everything
    | Var id -> Label(GRLabel (VarRef id), stack)
    | Prod (n,d,c) -> Label(ProdLabel, [d; c])
    | Lambda _ when Option.is_empty ts && List.is_empty stack -> Nothing
    | Lambda _ -> Everything
    | Sort _ -> Label(SortLabel, [])
    | Evar _ -> Everything
    | Case (_, _, _, _, _, c, _) ->
      begin
        match decomp stack c with
        | Label (GRLabel (ConstructRef _), _) -> Everything (* over-approximating w.r.t. [fMATCH] *)
        | Label _  | Nothing -> Label(CaseLabel, c :: stack)
        | Everything -> Everything
      end
    | Rel _ | Meta _ | LetIn _ | Fix _ | CoFix _
    | Int _ | Float _ | String _ | Array _ -> Nothing
  in
  decomp [] (eta_reduce sigma t)

let constr_pat_discr env ts p =
  let open GlobRef in
  let rec decomp stack p =
    match p with
    | PApp (f,args) -> decomp (Array.to_list args @ stack) f
    | PProj (p,c) when evaluable_projection p env ts -> None
    | PProj (p,c) -> Some (ProjLabel (Projection.repr p, 0), c :: stack)
    | PRef ((IndRef _) as ref)
    | PRef ((ConstructRef _ ) as ref) ->
      let ref = Environ.QGlobRef.canonize env ref in
      Some (GRLabel ref, stack)
    | PRef (VarRef v) when evaluable_named v env ts -> None
    | PRef ((VarRef _) as ref) -> Some (GRLabel ref, stack)
    | PRef (ConstRef c) when evaluable_constant c env ts -> None
    | PRef (ConstRef c) ->
      let c = Environ.QConstant.canonize env c in
      Some (label_of_opaque_constant c stack)
    | PVar v when evaluable_named v env ts -> None
    | PVar v -> Some (GRLabel (VarRef v), stack)
    | PProd (_,d,c) when stack = [] -> Some (ProdLabel, [d ; c])
    | PSort s when stack = [] -> Some (SortLabel, [])
    | PCase(_,_,p,_) | PIf(p,_,_) ->
      begin
        match decomp stack p with
        | Some (GRLabel (ConstructRef _), _) -> None (* over-approximating w.r.t. [fMATCH] *)
        | Some _ -> Some (CaseLabel, p :: stack)
        | None -> None
      end
    | _ -> None
  in
  decomp [] (eta_reduce_pat p)

let constr_pat_discr_syntactic env p =
  let open GlobRef in
  let rec decomp stack p =
    match eta_reduce_pat p with
    | PApp (f,args) -> decomp (Array.to_list args @ stack) f
    | PProj (p,c) -> Some (ProjLabel (Names.Projection.repr p, 0), c :: stack)
    | PRef ((IndRef _) as ref)
    | PRef ((ConstructRef _ ) as ref) ->
      let ref = Environ.QGlobRef.canonize env ref in
      Some (GRLabel ref, stack)
    | PRef ((VarRef _) as ref) -> Some (GRLabel ref, stack)
    | PRef (ConstRef c) ->
      let c = Environ.QConstant.canonize env c in
      Some (label_of_opaque_constant c stack)
    | PVar v -> Some (GRLabel (VarRef v), stack)
    | PProd (_,d,c) when stack = [] -> Some (ProdLabel, [d ; c])
    | PSort s when stack = [] -> Some (SortLabel, [])
    | _ -> None
  in
  decomp [] p

let bounded_constr_pat_discr env st (t,depth) =
  if Int.equal depth 0 then None
  else match constr_pat_discr env st t with
  | None -> None
  | Some (c,l) -> Some(c,List.map (fun c -> (c,depth-1)) l)

let bounded_constr_pat_discr_syntactic env (t,depth) =
  if Int.equal depth 0 then None
  else match constr_pat_discr_syntactic env t with
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

  let pattern_syntactic env pat =
    Dn.pattern (bounded_constr_pat_discr_syntactic env) (pat, !dnet_depth)

  let constr_pattern env sigma st pat =
    let mk p = match bounded_constr_val_discr env st sigma p with
    | Label l -> Some l
    | Everything | Nothing -> None
    in
    Dn.pattern mk (pat, !dnet_depth)

  let empty = Dn.empty
  let add = Dn.add
  let rmv = Dn.rmv

  let lookup env sigma st dn t =
    Dn.lookup dn (bounded_constr_val_discr env st sigma) (t,!dnet_depth)

end
