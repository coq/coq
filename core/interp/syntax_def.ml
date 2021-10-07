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

(* Syntactic definitions. *)

type syndef =
  { syndef_pattern : interpretation;
    syndef_onlyparsing : bool;
    syndef_deprecation : Deprecation.t option;
    syndef_also_in_cases_pattern : bool;
  }

let syntax_table =
  Summary.ref (KNmap.empty : syndef KNmap.t)
    ~name:"SYNDEFS"

let add_syntax_constant kn syndef =
  syntax_table := KNmap.add kn syndef !syntax_table

let load_syntax_constant i ((sp,kn),(_local,syndef)) =
  if Nametab.exists_cci sp then
    user_err ~hdr:"cache_syntax_constant"
      (Id.print (basename sp) ++ str " already exists");
  add_syntax_constant kn syndef;
  Nametab.push_syndef (Nametab.Until i) sp kn

let is_alias_of_already_visible_name sp = function
  | _,NRef (ref,_) ->
      let (dir,id) = repr_qualid (Nametab.shortest_qualid_of_global Id.Set.empty ref) in
      DirPath.is_empty dir && Id.equal id (basename sp)
  | _ ->
      false

let open_syntax_constant i ((sp,kn),(_local,syndef)) =
  let pat = syndef.syndef_pattern in
  if not (Int.equal i 1 && is_alias_of_already_visible_name sp pat) then begin
    Nametab.push_syndef (Nametab.Exactly i) sp kn;
    if not syndef.syndef_onlyparsing then
      (* Redeclare it to be used as (short) name in case an other (distfix)
         notation was declared in between *)
      Notation.declare_uninterpretation ~also_in_cases_pattern:syndef.syndef_also_in_cases_pattern (Notation.SynDefRule kn) pat
  end

let import_syntax_constant i sp kn =
  let syndef = KNmap.get kn !syntax_table in
  open_syntax_constant i ((sp,kn),(false,syndef))

let cache_syntax_constant d =
  load_syntax_constant 1 d;
  open_syntax_constant 1 d

let subst_syntax_constant (subst,(local,syndef)) =
  let syndef_pattern = Notation_ops.subst_interpretation subst syndef.syndef_pattern in
  (local, { syndef with syndef_pattern })

let classify_syntax_constant (local,_ as o) =
  if local then Dispose else Substitute o

let filtered_open_syntax_constant f i ((_,kn),_ as o) =
  let in_f = match f with
    | Unfiltered -> true
  in
  if in_f then open_syntax_constant i o

let in_syntax_constant : (bool * syndef) -> obj =
  declare_object {(default_object "SYNDEF") with
    cache_function = cache_syntax_constant;
    load_function = load_syntax_constant;
    open_function = filtered_open_syntax_constant;
    subst_function = subst_syntax_constant;
    classify_function = classify_syntax_constant }

let declare_syntactic_definition ~local ?(also_in_cases_pattern=true) deprecation id ~onlyparsing pat =
  let syndef =
    { syndef_pattern = pat;
      syndef_onlyparsing = onlyparsing;
      syndef_deprecation = deprecation;
      syndef_also_in_cases_pattern = also_in_cases_pattern;
    }
  in
  let _ = add_leaf id (in_syntax_constant (local,syndef)) in ()

let pr_syndef kn = pr_qualid (Nametab.shortest_qualid_of_syndef Id.Set.empty kn)

let warn_deprecated_syntactic_definition =
  Deprecation.create_warning ~object_name:"Notation" ~warning_name:"deprecated-syntactic-definition"
    pr_syndef

let search_syntactic_definition ?loc kn =
  let syndef = KNmap.find kn !syntax_table in
  Option.iter (fun d -> warn_deprecated_syntactic_definition ?loc (kn,d)) syndef.syndef_deprecation;
  syndef.syndef_pattern

let search_filtered_syntactic_definition ?loc filter kn =
  let syndef = KNmap.find kn !syntax_table in
  let res = filter syndef.syndef_pattern in
  if Option.has_some res then
    Option.iter (fun d -> warn_deprecated_syntactic_definition ?loc (kn,d)) syndef.syndef_deprecation;
  res
