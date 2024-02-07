(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let s2l s = Label.of_id (Id.of_string s)

let mk file modules label =
  let dp = DirPath.make (List.map Id.of_string [file; "Ltac2"]) in
  let mp = List.fold_left (fun mp modname -> MPdot (mp, s2l modname)) (MPfile dp) modules in
  KerName.make mp (s2l label)

let mk_init n = mk "Init" [] n

let mk_std n = mk "Std" [] n

module Types = struct
  let unit = mk_init "unit"
  let list = mk_init "list"
  let int = mk_init "int"
  let string = mk_init "string"
  let char = mk_init "char"
  let ident = mk_init "ident"
  let uint63 = mk_init "uint63"
  let float = mk_init "float"
  let meta = mk_init "meta"
  let evar = mk_init "evar"
  let sort = mk_init "sort"
  let cast = mk_init "cast"
  let instance = mk_init "instance"
  let constant = mk_init "constant"
  let inductive = mk_init "inductive"
  let constructor = mk_init "constructor"
  let projection = mk_init "projection"
  let pattern = mk_init "pattern"
  let constr = mk_init "constr"
  let preterm = mk_init "preterm"
  let binder = mk_init "binder"
  let message = mk_init "message"
  let format = mk_init "format"
  let exn = mk_init "exn"
  let array = mk_init "array"
  let option = mk_init "option"
  let bool = mk_init "bool"
  let result = mk_init "result"
  let err = mk_init "err"
  let exninfo = mk_init "exninfo"

  let reference = mk_std "reference"
  let occurrences = mk_std "occurrences"
  let intro_pattern = mk_std "intro_pattern"
  let bindings = mk_std "bindings"
  let assertion = mk_std "assertion"
  let clause = mk_std "clause"
  let induction_clause = mk_std "induction_clause"
  let red_flags = mk_std "red_flags"
  let rewriting = mk_std "rewriting"
  let inversion_kind = mk_std "inversion_kind"
  let destruction_arg = mk_std "destruction_arg"
  let move_location = mk_std "move_location"
  let hypothesis = mk_std "hypothesis"
  let std_debug = mk_std "debug"
  let std_strategy = mk_std "strategy"
  let orientation = mk_std "orientation"

  let transparent_state = mk "TransparentState" [] "t"

  let relevance = mk "Constr" ["Binder"] "relevance"

  let constr_kind = mk "Constr" ["Unsafe"] "kind"
  let constr_case = mk "Constr" ["Unsafe"] "case"

  let pretype_flags = mk "Constr" ["Pretype";"Flags"] "t"

  let pretype_expected_type = mk "Constr" ["Pretype"] "expected_type"

  let matching_context = mk "Pattern" [] "context"

  let match_kind = mk "Pattern" [] "match_kind"

  let free = mk "Fresh" ["Free"] "t"

  let ind_data = mk "Ind" [] "data"

  let map_tag = mk "FSet" ["Tags"] "tag"

  let fset = mk "FSet" [] "t"
  let fmap = mk "FMap" [] "t"
end
