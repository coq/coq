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
open Notationextern

(* Abbreviations. *)

type abbreviation =
  { abbrev_pattern : interpretation;
    abbrev_onlyparsing : bool;
    abbrev_deprecation : Deprecation.t option;
    abbrev_also_in_cases_pattern : bool;
    abbrev_activated : bool; (* Not really necessary in practice *)
  }

let abbrev_table =
  Summary.ref (KNmap.empty : (full_path * abbreviation) KNmap.t)
    ~name:"ABBREVIATIONS"

let add_abbreviation kn sp abbrev =
  abbrev_table := KNmap.add kn (sp,abbrev) !abbrev_table

let toggle_abbreviation ~on ~use kn =
  let sp, data = KNmap.find kn !abbrev_table in
  if data.abbrev_activated != on then
    begin
      abbrev_table := KNmap.add kn (sp, {data with abbrev_activated = on}) !abbrev_table;
      match use with
      | OnlyPrinting -> ()
      | OnlyParsing | ParsingAndPrinting ->
         if on then
           begin
             Nametab.Abbrev.push ?deprecated:data.abbrev_deprecation (Nametab.Until 1) sp kn;
             Nametab.Abbrev.push (Nametab.Exactly 1) sp kn
           end
         else
           Nametab.Abbrev.remove sp kn
    end

let toggle_abbreviations ~on ~use filter =
  KNmap.fold (fun kn (sp,abbrev) () ->
      if abbrev.abbrev_activated != on && filter sp abbrev.abbrev_pattern then toggle_abbreviation ~on ~use kn)
  !abbrev_table ()

let load_abbreviation i ((sp,kn),(_local,abbrev)) =
  if Nametab.GlobRef.exists sp then
    user_err
      (Id.print (basename sp) ++ str " already exists.");
  add_abbreviation kn sp abbrev;
  Nametab.Abbrev.push ?deprecated:abbrev.abbrev_deprecation (Nametab.Until i) sp kn

let is_alias_of_already_visible_name sp = function
  | _,NRef (ref,None) ->
      let (dir,id) = repr_qualid (Nametab.GlobRef.shortest_qualid Id.Set.empty ref) in
      DirPath.is_empty dir && Id.equal id (basename sp)
  | _ ->
      false

let open_abbreviation i ((sp,kn),(_local,abbrev)) =
  let pat = abbrev.abbrev_pattern in
  if not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then begin
    Nametab.Abbrev.push (Nametab.Exactly i) sp kn;
    if not abbrev.abbrev_onlyparsing then
      (* Redeclare it to be used as (short) name in case an other (distfix)
         notation was declared in between *)
      Notationextern.declare_uninterpretation ~also_in_cases_pattern:abbrev.abbrev_also_in_cases_pattern (AbbrevRule kn) pat
  end

let import_abbreviation i sp kn =
  let _,abbrev = KNmap.get kn !abbrev_table in
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
      abbrev_activated = true;
    }
  in
  add_leaf (inAbbreviation id (local,abbrev))

(* Remark: do not check for activation (if not activated, it is already not supposed to be located) *)
let search_abbreviation kn =
  let _,abbrev = KNmap.find kn !abbrev_table in
  abbrev.abbrev_pattern

let search_filtered_abbreviation filter kn =
  let _,abbrev = KNmap.find kn !abbrev_table in
  let res = filter abbrev.abbrev_pattern in
  res
