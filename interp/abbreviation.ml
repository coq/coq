(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Libnames
open Libobject
open Lib
open Notation_term

(* Abbreviations. *)

type abbreviation =
  { abbrev_pattern : interpretation;
    abbrev_onlyparsing : bool;
    abbrev_deprecation : Deprecation.t option;
    abbrev_also_in_cases_pattern : bool;
  }

let abbrev_table =
  Summary.ref (KNmap.empty : abbreviation KNmap.t)
    ~name:"ABBREVIATIONS"

let add_abbreviation kn abbrev =
  abbrev_table := KNmap.add kn abbrev !abbrev_table

let load_abbreviation i ((sp,kn),(_local,abbrev)) =
  if Nametab.exists_cci sp then
    user_err
      (Id.print (basename sp) ++ str " already exists.");
  add_abbreviation kn abbrev;
  Nametab.push_abbreviation (Nametab.Until i) sp kn

let is_alias_of_already_visible_name sp = function
  | _,NRef (ref,_) ->
      let (dir,id) = repr_qualid (Nametab.shortest_qualid_of_global Id.Set.empty ref) in
      DirPath.is_empty dir && Id.equal id (basename sp)
  | _ ->
      false

let open_abbreviation i ((sp,kn),(_local,abbrev)) =
  let pat = abbrev.abbrev_pattern in
  if not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then begin
    Nametab.push_abbreviation (Nametab.Exactly i) sp kn;
    if not abbrev.abbrev_onlyparsing then
      (* Redeclare it to be used as (short) name in case an other (distfix)
         notation was declared in between *)
      Notation.declare_uninterpretation ~also_in_cases_pattern:abbrev.abbrev_also_in_cases_pattern (AbbrevRule kn) pat
  end

let import_abbreviation i sp kn =
  let abbrev = KNmap.get kn !abbrev_table in
  open_abbreviation i ((sp,kn),(false,abbrev))

let cache_abbreviation d =
  load_abbreviation 1 d;
  open_abbreviation 1 d

let subst_abbreviation (subst,(local,abbrev)) =
  let abbrev_pattern = Notation_ops.subst_interpretation subst abbrev.abbrev_pattern in
  (local, { abbrev with abbrev_pattern })

let classify_abbreviation (local,_) =
  if local then Dispose else Substitute

let inAbbreviation : Id.t -> (bool * abbreviation) -> obj =
  declare_named_object {(default_object "ABBREVIATION") with
    cache_function = cache_abbreviation;
    load_function = load_abbreviation;
    open_function = simple_open open_abbreviation;
    subst_function = subst_abbreviation;
    classify_function = classify_abbreviation }

let declare_abbreviation ~local ?(also_in_cases_pattern=true) deprecation id ~onlyparsing pat =
  let abbrev =
    { abbrev_pattern = pat;
      abbrev_onlyparsing = onlyparsing;
      abbrev_deprecation = deprecation;
      abbrev_also_in_cases_pattern = also_in_cases_pattern;
    }
  in
  add_leaf (inAbbreviation id (local,abbrev))

let pr_abbreviation kn = pr_qualid (Nametab.shortest_qualid_of_abbreviation Id.Set.empty kn)

let warn_deprecated_abbreviation =
  Deprecation.create_warning ~object_name:"Notation" ~warning_name:"deprecated-syntactic-definition"
    pr_abbreviation

let search_abbreviation ?loc kn =
  let abbrev = KNmap.find kn !abbrev_table in
  Option.iter (fun d -> warn_deprecated_abbreviation ?loc (kn,d)) abbrev.abbrev_deprecation;
  abbrev.abbrev_pattern

let search_filtered_abbreviation ?loc filter kn =
  let abbrev = KNmap.find kn !abbrev_table in
  let res = filter abbrev.abbrev_pattern in
  if Option.has_some res then
    Option.iter (fun d -> warn_deprecated_abbreviation ?loc (kn,d)) abbrev.abbrev_deprecation;
  res
