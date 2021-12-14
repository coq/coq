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
open Locus

(** Utilities on or_var *)

let or_var_map f = function
  | ArgArg x -> ArgArg (f x)
  | ArgVar _ as y -> y

(** Utilities on occurrences *)

let occurrences_map f = function
  | OnlyOccurrences l ->
    let l' = f l in
    if l' = [] then NoOccurrences else OnlyOccurrences l'
  | AllOccurrencesBut l ->
    let l' = f l in
    if l' = [] then AllOccurrences else AllOccurrencesBut l'
  | (NoOccurrences|AllOccurrences|AtLeastOneOccurrence) as o -> o

type occurrences_count = {current: int; remaining: int list; where: (bool * int)}

let error_invalid_occurrence l =
  CErrors.user_err Pp.(str ("Invalid occurrence " ^ String.plural (List.length l) "number" ^": ")
  ++ prlist_with_sep spc int l ++ str ".")

let initialize_occurrence_counter occs =
  let (nowhere_except_in,occs) =
    match occs with
    | AtLeastOneOccurrence -> (false,[])
    | AllOccurrences -> (false,[])
    | AllOccurrencesBut l -> (false,List.sort_uniquize Int.compare l)
    | NoOccurrences -> (true,[])
    | OnlyOccurrences l -> (true,List.sort_uniquize Int.compare l) in
  let max =
    match occs with
    | n::_ when n <= 0 -> error_invalid_occurrence [n]
    | [] -> 0
    | _ -> Util.List.last occs in
  {current = 0; remaining = occs; where = (nowhere_except_in,max)}

let update_occurrence_counter {current; remaining; where = (nowhere_except_in,_ as where)} =
  let current = succ current in
  match remaining with
  | occ::remaining when Int.equal current occ -> (nowhere_except_in,{current;remaining;where})
  | _ -> (not nowhere_except_in,{current;remaining;where})

let check_used_occurrences {remaining} =
  if not (Util.List.is_empty remaining) then error_invalid_occurrence remaining

let occurrences_done {current; where = (nowhere_except_in,max)} =
  nowhere_except_in && current > max

let current_occurrence {current} = current

let more_specific_occurrences {current; where = (_,max)} =
  current <= max

let is_selected occ = function
  | AtLeastOneOccurrence -> true
  | AllOccurrences -> true
  | AllOccurrencesBut l -> not (Int.List.mem occ l)
  | OnlyOccurrences l -> Int.List.mem occ l
  | NoOccurrences -> false

(** Usual clauses *)

let allHypsAndConcl = { onhyps=None; concl_occs=AllOccurrences }
let allHyps = { onhyps=None; concl_occs=NoOccurrences }
let onConcl = { onhyps=Some[]; concl_occs=AllOccurrences }
let nowhere = { onhyps=Some[]; concl_occs=NoOccurrences }
let onHyp h =
  { onhyps=Some[(AllOccurrences,h),InHyp]; concl_occs=NoOccurrences }

let is_nowhere = function
| { onhyps=Some[]; concl_occs=NoOccurrences } -> true
| _ -> false

let is_all_occurrences = function
  | AtLeastOneOccurrence
  | AllOccurrences -> true
  | _ -> false

(** Clause conversion functions, parametrized by a hyp enumeration function *)

(** From [clause] to [simple_clause] *)

let simple_clause_of enum_hyps cl =
  let error_occurrences () =
    CErrors.user_err Pp.(str "This tactic does not support occurrences selection") in
  let error_body_selection () =
    CErrors.user_err Pp.(str "This tactic does not support body selection") in
  let hyps =
    match cl.onhyps with
    | None ->
        List.map Option.make (enum_hyps ())
    | Some l ->
        List.map (fun ((occs,id),w) ->
          if not (is_all_occurrences occs) then error_occurrences ();
          if w = InHypValueOnly then error_body_selection ();
          Some id) l in
  if cl.concl_occs = NoOccurrences then hyps
  else
    if not (is_all_occurrences cl.concl_occs) then error_occurrences ()
    else None :: hyps

(** From [clause] to [concrete_clause] *)

let concrete_clause_of enum_hyps cl =
  let hyps =
    match cl.onhyps with
    | None ->
        let f id = OnHyp (id,AllOccurrences,InHyp) in
        List.map f (enum_hyps ())
    | Some l ->
        List.map (fun ((occs,id),w) -> OnHyp (id,occs,w)) l in
  if cl.concl_occs = NoOccurrences then hyps
  else
    OnConcl cl.concl_occs :: hyps

(** Miscellaneous functions *)

let out_arg = function
  | ArgVar _ -> CErrors.anomaly (Pp.str "Unevaluated or_var variable.")
  | ArgArg x -> x

let occurrences_of_hyp id cls =
  let rec hyp_occ = function
      [] -> NoOccurrences, InHyp
    | ((occs,id'),hl)::_ when Names.Id.equal id id' ->
        occurrences_map (List.map out_arg) occs, hl
    | _::l -> hyp_occ l in
  match cls.onhyps with
      None -> AllOccurrences,InHyp
    | Some l -> hyp_occ l

let occurrences_of_goal cls =
  occurrences_map (List.map out_arg) cls.concl_occs

let in_every_hyp cls = Option.is_empty cls.onhyps

let clause_with_generic_occurrences cls =
  let hyps = match cls.onhyps with
  | None -> true
  | Some hyps ->
     List.for_all
       (function ((AllOccurrences,_),_) -> true | _ -> false) hyps in
  let concl = match cls.concl_occs with
  | AtLeastOneOccurrence | AllOccurrences | NoOccurrences -> true
  | _ -> false in
  hyps && concl

let clause_with_generic_context_selection cls =
  let hyps = match cls.onhyps with
  | None -> true
  | Some hyps ->
     List.for_all
       (function ((AllOccurrences,_),InHyp) -> true | _ -> false) hyps in
  let concl = match cls.concl_occs with
  | AtLeastOneOccurrence | AllOccurrences | NoOccurrences -> true
  | _ -> false in
  hyps && concl
