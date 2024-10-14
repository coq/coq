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
open Names
open Locus
open EConstr
open Termops
open Pretype_errors

module NamedDecl = Context.Named.Declaration

(** Processing occurrences *)

let explain_incorrect_in_value_occurrence id =
  Id.print id ++ str " has no value."

let proceed_with_occurrences f occs x =
  match occs with
  | NoOccurrences -> x
  | occs ->
    let (occs,x) = f (Locusops.initialize_occurrence_counter occs) x in
    Locusops.check_used_occurrences occs;
    x

(** Applying a function over a named_declaration with an hypothesis
    location request *)

let map_named_declaration_with_hyploc f hyploc acc decl =
  let open Context.Named.Declaration in
  let f acc typ =
    let acc, typ = f (Some (NamedDecl.get_id decl, hyploc)) acc typ in
    acc, typ
  in
  match decl,hyploc with
  | LocalAssum (id,_), InHypValueOnly ->
      user_err (explain_incorrect_in_value_occurrence id.Context.binder_name)
  | LocalAssum (id,typ), _ ->
      let acc,typ = f acc typ in acc, LocalAssum (id,typ)
  | LocalDef (id,body,typ), InHypTypeOnly ->
      let acc,typ = f acc typ in acc, LocalDef (id,body,typ)
  | LocalDef (id,body,typ), InHypValueOnly ->
      let acc,body = f acc body in acc, LocalDef (id,body,typ)
  | LocalDef (id,body,typ), InHyp ->
      let acc,body = f acc body in
      let acc,typ = f acc typ in
      acc, LocalDef (id,body,typ)

(** Finding a subterm up to some testing function *)

exception SubtermUnificationError of subterm_unification_error

type ('a, 'b) testing_function = {
  match_fun : int -> 'a -> EConstr.constr -> ('b, unit) Result.t;
  merge_fun : 'b -> 'a -> ('a, unit) Result.t;
  mutable testing_state : 'a;
  mutable last_found : position_reporting option
}

(* Find subterms using a testing function, but only at a list of
   locations or excluding a list of locations; in the occurrences list
   (b,l), b=true means no occurrence except the ones in l and b=false,
   means all occurrences except the ones in l *)

let replace_term_occ_gen_modulo env sigma like_first test bywhat cl count t =
  let count = ref count in
  let rec substrec (nested, k) t =
    if Locusops.occurrences_done !count then t else
    match test.match_fun k test.testing_state t with
    | Result.Ok subst ->
      let selected, count' = Locusops.update_occurrence_counter !count in
      let () = count := count' in
      if selected then
        let pos = Locusops.current_occurrence !count in
        if nested then
          (* in case it is nested but not later detected as unconvertible,
             as when matching "id _" in "id (id 0)" *)
          let lastpos = Option.get test.last_found in
          raise (SubtermUnificationError (nested, ((cl, pos), t), lastpos))
        else match test.merge_fun subst test.testing_state with
        | Result.Ok state ->
          let () = test.testing_state <- state in
          let () = test.last_found <- Some ((cl, pos), t) in
          (* Check nested matching subterms *)
          let () =
            if Locusops.more_specific_occurrences !count then
              ignore (subst_below (true, k) t)
          in
          Vars.lift k (bywhat ())
        | Result.Error () ->
          if like_first then subst_below (nested, k) t
          else
            let lastpos = Option.get test.last_found in
            raise (SubtermUnificationError (nested, ((cl, pos), t), lastpos))
      else
        subst_below (nested, k) t
    | Result.Error () ->
      subst_below (nested, k) t
  and subst_below k t =
    map_constr_with_binders_left_to_right env sigma (fun d (nested, k) -> (nested, k + 1)) substrec k t
  in
  let t' = substrec (false, 0) t in
  (!count, t')

let replace_term_occ_modulo env evd occs test bywhat t =
  let occs',like_first =
    match occs with AtOccs occs -> occs,false | LikeFirst -> AllOccurrences,true in
  proceed_with_occurrences
    (replace_term_occ_gen_modulo env evd like_first test bywhat None) occs' t

let replace_term_occ_decl_modulo env evd occs test bywhat d =
  let (plocs,hyploc),like_first =
    match occs with AtOccs occs -> occs,false | LikeFirst -> (AllOccurrences,InHyp),true in
  proceed_with_occurrences
    (map_named_declaration_with_hyploc
       (replace_term_occ_gen_modulo env evd like_first test bywhat)
       hyploc)
    plocs d

(** Finding an exact subterm *)

let make_eq_univs_test env evd c =
  { match_fun = (fun k evd c' ->
    match EConstr.eq_constr_universes_proj env evd c c' with
    | None -> Result.Error ()
    | Some cst ->
      try Result.Ok (Evd.add_universe_constraints evd cst)
      with Evd.UniversesDiffer | UGraph.UniverseInconsistency _ -> Result.Error ()
    );
  merge_fun = (fun evd _ -> Result.Ok evd);
  testing_state = evd;
  last_found = None
}

let subst_closed_term_occ env evd occs c t =
  let test = make_eq_univs_test env evd c in
  let bywhat () = mkRel 1 in
  let t' = replace_term_occ_modulo env evd occs test bywhat t in
    t', test.testing_state

let subst_closed_term_occ_decl env evd occs c d =
  let test = make_eq_univs_test env evd c in
  let (plocs,hyploc),like_first =
    match occs with AtOccs occs -> occs,false | LikeFirst -> (AllOccurrences,InHyp),true in
  let bywhat () = mkRel 1 in
  proceed_with_occurrences
    (map_named_declaration_with_hyploc
       (fun _ -> replace_term_occ_gen_modulo env evd like_first test bywhat None)
       hyploc) plocs d,
  test.testing_state
