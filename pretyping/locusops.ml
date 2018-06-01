(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Locus

(** Utilities on occurrences *)

let occurrences_map f = function
  | OnlyOccurrences l ->
    let l' = f l in
    if l' = [] then NoOccurrences else OnlyOccurrences l'
  | AllOccurrencesBut l ->
    let l' = f l in
    if l' = [] then AllOccurrences else AllOccurrencesBut l'
  | (NoOccurrences|AllOccurrences) as o -> o

let convert_occs = function
  | AllOccurrences -> (false,[])
  | AllOccurrencesBut l -> (false,l)
  | NoOccurrences -> (true,[])
  | OnlyOccurrences l -> (true,l)

let is_selected occ = function
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
	  if occs <> AllOccurrences then error_occurrences ();
	  if w = InHypValueOnly then error_body_selection ();
	  Some id) l in
  if cl.concl_occs = NoOccurrences then hyps
  else
    if cl.concl_occs <> AllOccurrences then error_occurrences ()
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
  | AllOccurrences | NoOccurrences -> true
  | _ -> false in
  hyps && concl

let clause_with_generic_context_selection cls =
  let hyps = match cls.onhyps with
  | None -> true
  | Some hyps ->
     List.for_all
       (function ((AllOccurrences,_),InHyp) -> true | _ -> false) hyps in
  let concl = match cls.concl_occs with
  | AllOccurrences | NoOccurrences -> true
  | _ -> false in
  hyps && concl
