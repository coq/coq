(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let legacy_to_findlib = [
  ("btauto_plugin",                 ["plugins";"btauto"]) ;
  ("derive_plugin",                 ["plugins";"derive"]) ;
  ("firstorder_plugin",             ["plugins";"firstorder"]) ;
  ("ltac_plugin",                   ["plugins";"ltac"]) ;
  ("micromega_plugin",              ["plugins";"micromega"]) ;
  ("ring_plugin",                   ["plugins";"ring"]) ;
  ("ssr_plugin",                    ["plugins";"ssr"]) ;
  ("syntax_plugin",                 ["plugins";"syntax"]) ;
  ("cc_plugin",                     ["plugins";"cc"]) ;
  ("extraction_plugin",             ["plugins";"extraction"]) ;
  ("funind_plugin",                 ["plugins";"funind"]) ;
  ("ltac2_plugin",                  ["plugins";"ltac2"]) ;
  ("nsatz_plugin",                  ["plugins";"nsatz"]) ;
  ("rtauto_plugin",                 ["plugins";"rtauto"]) ;
  ("ssrmatching_plugin",            ["plugins";"ssrmatching"]) ;
  ("ssreflect_plugin",              ["plugins";"ssreflect"]) ;
  ("number_string_notation_plugin", ["plugins";"number_string_notation"]) ;
  ("zify_plugin",                   ["plugins";"zify"]) ;
  ("tauto_plugin",                  ["plugins";"tauto"]) ;
]
