(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Nameops
open Termops
open Environ
open Reductionops

module NamedDecl = Context.Named.Declaration

type refiner_error =

  (* Errors raised by the refiner *)
  | UnresolvedBindings of Name.t list
  | CannotApply of EConstr.t * EConstr.t
  | NonLinearProof of EConstr.t

  (* Errors raised by the tactics *)
  | IntroNeedsProduct
  | NoSuchHyp of Id.t

exception RefinerError of Environ.env * Evd.evar_map * refiner_error


let error_no_such_hypothesis env sigma id = raise (RefinerError (env, sigma, NoSuchHyp id))

(************************************************************************)
(************************************************************************)
(* Implementation of the structural rules (moving and deleting
   hypotheses around) *)

(* The ClearBody tactic *)

(* Reordering of the context *)

(* faire le minimum d'echanges pour que l'ordre donne soit un *)
(* sous-ordre du resultat. Par exemple, 2 hyps non mentionnee ne sont *)
(* pas echangees. Choix: les hyps mentionnees ne peuvent qu'etre *)
(* reculees par rapport aux autres (faire le contraire!) *)

let mt_q = (Id.Map.empty,[])
let push_val y = function
    (_,[] as q) -> q
  | (m, (x,l)::q) -> (m, (x,Id.Set.add y l)::q)
let push_item x v (m,l) =
  (Id.Map.add x v m, (x,Id.Set.empty)::l)
let mem_q x (m,_) = Id.Map.mem x m
let find_q x (m,q) =
  let v = Id.Map.find x m in
  let m' = Id.Map.remove x m in
  let rec find accs acc = function
      [] -> raise Not_found
    | [(x',l)] ->
        if Id.equal x x' then ((v,Id.Set.union accs l),(m',List.rev acc))
        else raise Not_found
    | (x',l as i)::((x'',l'')::q as itl) ->
        if Id.equal x x' then
          ((v,Id.Set.union accs l),
           (m',List.rev acc@(x'',Id.Set.add x (Id.Set.union l l''))::q))
        else find (Id.Set.union l accs) (i::acc) itl in
  find Id.Set.empty [] q

let occur_vars_in_decl env sigma hyps d =
  if Id.Set.is_empty hyps then false else
    let ohyps = global_vars_set_of_decl env sigma d in
    Id.Set.exists (fun h -> Id.Set.mem h ohyps) hyps

let reorder_context env sigma sign ord =
  let ords = List.fold_right Id.Set.add ord Id.Set.empty in
  if not (Int.equal (List.length ord) (Id.Set.cardinal ords)) then
    user_err Pp.(str "Order list has duplicates");
  let rec step ord expected ctxt_head moved_hyps ctxt_tail =
    match ord with
      | [] -> List.rev ctxt_tail @ ctxt_head
      | top::ord' when mem_q top moved_hyps ->
          let ((d,h),mh) = find_q top moved_hyps in
          if occur_vars_in_decl env sigma h d then
            user_err
              (str "Cannot move declaration " ++ Id.print top ++ spc() ++
              str "before " ++
              pr_sequence Id.print
                (Id.Set.elements (Id.Set.inter h
                  (global_vars_set_of_decl env sigma d))) ++ str ".");
          step ord' expected ctxt_head mh (d::ctxt_tail)
      | _ ->
          (match ctxt_head with
            | [] -> error_no_such_hypothesis env sigma (List.hd ord)
            | d :: ctxt ->
                let x = NamedDecl.get_id d in
                if Id.Set.mem x expected then
                  step ord (Id.Set.remove x expected)
                    ctxt (push_item x d moved_hyps) ctxt_tail
                else
                  step ord expected
                    ctxt (push_val x moved_hyps) (d::ctxt_tail)) in
  step ord ords sign mt_q []

let reorder_val_context env sigma sign ord =
match ord with
| [] | [_] ->
  (* Single variable-free definitions need not be reordered *)
  sign
| _ :: _ :: _ ->
  let open EConstr in
  val_of_named_context (reorder_context env sigma (named_context_of_val sign) ord)

let check_decl_position env sigma sign d =
  let open EConstr in
  let x = NamedDecl.get_id d in
  let needed = global_vars_set_of_decl env sigma d in
  let deps = dependency_closure env sigma (named_context_of_val sign) needed in
  if Id.List.mem x deps then
    user_err
      (str "Cannot create self-referring hypothesis " ++ Id.print x ++ str ".");
  x::deps

(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_hyp with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] at location [hto] which belongs to the hyps on the
 * left side [left] of the full signature if [toleft=true] or to the hyps
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

(** Printing of [move_location] *)

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveFirst -> str " at top"
  | MoveLast -> str " at bottom"

let move_location_eq m1 m2 = match m1, m2 with
| MoveAfter id1, MoveAfter id2 -> Id.equal id1 id2
| MoveBefore id1, MoveBefore id2 -> Id.equal id1 id2
| MoveLast, MoveLast -> true
| MoveFirst, MoveFirst -> true
| _ -> false

let mem_id_context id ctx = Id.Map.mem id ctx.Environ.env_named_map

let split_sign env sigma hfrom l =
  let () = if not (mem_id_context hfrom l) then error_no_such_hypothesis env sigma hfrom in
  let rec splitrec left sign = match EConstr.match_named_context_val sign with
  | None -> assert false
  | Some (d, right) ->
    let hyp = NamedDecl.get_id d in
    if Id.equal hyp hfrom then (left, right, d)
    else splitrec (d :: left) right
  in
  splitrec [] l

(* ocaml/ocaml#10027 triggered if inline record *)
type cannot_move_hyp = { from : Id.t; hto : Id.t move_location; hyp : Id.t }
exception CannotMoveHyp of cannot_move_hyp

let () = CErrors.register_handler (function
    | CannotMoveHyp { from; hto; hyp } ->
      Some Pp.(str "Cannot move " ++ Id.print from ++
               pr_move_location Id.print hto ++
               str ": it occurs in the declaration of " ++
               Id.print hyp ++ str ".")
    | _ -> None)

let move_hyp env sigma toleft (left,declfrom,right) hto =
  let open EConstr in
  let push prefix sign = List.fold_right push_named_context_val prefix sign in
  let push_rev prefix sign = List.fold_left (fun accu d -> push_named_context_val d accu) sign prefix in
  let rec moverec_toleft ans first middle midvars = function
    | [] -> push middle @@ push first ans
    | d :: _ as right when move_location_eq hto (MoveBefore (NamedDecl.get_id d)) ->
      push_rev right @@ push middle @@ push first ans
    | d :: right ->
        let hyp = NamedDecl.get_id d in
        let (first', middle', midvars') =
          if occur_vars_in_decl env sigma midvars d then
            if not (move_location_eq hto (MoveAfter hyp)) then
              (first, d :: middle, Id.Set.add hyp midvars)
            else raise (CannotMoveHyp {from = NamedDecl.get_id declfrom; hto; hyp})
          else
            (d::first, middle, midvars)
        in
        if move_location_eq hto (MoveAfter hyp) then
          push_rev right @@ push middle' @@ push first' ans
        else
          moverec_toleft ans first' middle' midvars' right
  in
  let rec moverec_toright first middle depvars right = match EConstr.match_named_context_val right with
    | None -> push_rev first @@ push_rev middle right
    | Some (d, _) when move_location_eq hto (MoveBefore (NamedDecl.get_id d)) ->
        push_rev first @@ push_rev middle @@ right
    | Some (d, right) ->
        let hyp = NamedDecl.get_id d in
        let (first', middle', depvars') =
          if Id.Set.mem hyp depvars then
            if not (move_location_eq hto (MoveAfter hyp)) then
              let vars = global_vars_set_of_decl env sigma d in
              let depvars = Id.Set.union vars depvars in
              (first, d::middle, depvars)
            else raise (CannotMoveHyp {from = NamedDecl.get_id declfrom; hto; hyp})
          else
            (d::first, middle, depvars)
        in
        if move_location_eq hto (MoveAfter hyp) then
          push_rev first' @@ push_rev middle' @@ right
        else
          moverec_toright first' middle' depvars' right
  in
  if toleft then
    let id = NamedDecl.get_id declfrom in
    moverec_toleft right [] [declfrom] (Id.Set.singleton id) left
  else
    let depvars = global_vars_set_of_decl env sigma declfrom in
    let right = moverec_toright [] [declfrom] depvars right in
    push_rev left @@ right

let move_hyp_in_named_context env sigma hfrom hto sign =
  let (left, right, declfrom) = split_sign env sigma hfrom sign in
  let toleft = match hto with
  | MoveLast -> true
  | MoveAfter id | MoveBefore id ->
    if mem_id_context id right then false
    else if mem_id_context id sign then true
    else error_no_such_hypothesis env sigma id
  | MoveFirst -> false
  in
  move_hyp env sigma toleft (left,declfrom,right) hto

let insert_decl_in_named_context env sigma decl hto sign =
  move_hyp env sigma false ([],decl,sign) hto

let convert_hyp ~check ~reorder env sigma d =
  let id = NamedDecl.get_id d in
  let b = NamedDecl.get_value d in
  let sign = Environ.named_context_val env in
  match lookup_named_ctxt id sign with
  | exception Not_found ->
    if check then error_no_such_hypothesis env sigma id
    else sign
  | d' ->
    let c = Option.map EConstr.of_constr (NamedDecl.get_value d') in
    if check && not (is_conv env sigma (NamedDecl.get_type d) (EConstr.of_constr (NamedDecl.get_type d'))) then
      user_err
        (str "Incorrect change of the type of " ++ Id.print id ++ str ".");
    if check && not (Option.equal (is_conv env sigma) b c) then
      user_err
        (str "Incorrect change of the body of "++ Id.print id ++ str ".");
    let sign' = apply_to_hyp sign id (fun _ _ _ -> EConstr.Unsafe.to_named_decl d) in
    if reorder then reorder_val_context env sigma sign' (check_decl_position env sigma sign d)
    else sign'
