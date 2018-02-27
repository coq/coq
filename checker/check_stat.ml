(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Cic
open Declarations
open Environ

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then begin
    Format.printf "total heap size = %d kbytes\n" (CObj.heap_size_kb ());
    Format.print_newline();
    Format.print_flush()
  end

let output_context = ref false

let pr_engagement impr_set =
  begin
    match impr_set with
    | ImpredicativeSet -> str "Theory: Set is impredicative"
    | PredicativeSet -> str "Theory: Set is predicative"
  end

let cst_filter f csts =
  Cmap_env.fold
    (fun c ce acc -> if f c ce then c::acc else acc)
    csts []

let is_ax _ cb = not (constant_has_body cb)

let pr_ax csts =
  let axs = cst_filter is_ax csts in
  if axs = [] then
    str "Axioms: <none>"
  else
    hv 2 (str "Axioms:" ++ fnl() ++ prlist_with_sep fnl Indtypes.prcon axs)

let print_context env =
  if !output_context then begin
    let
      {env_globals=
        {env_constants=csts; env_inductives=inds;
         env_modules=mods; env_modtypes=mtys};
       env_stratification=
        {env_universes=univ; env_engagement=engt}} = env in
    Feedback.msg_notice
      (hov 0
      (fnl() ++ str"CONTEXT SUMMARY" ++ fnl() ++
      str"===============" ++ fnl() ++ fnl() ++
      str "* " ++ hov 0 (pr_engagement engt ++ fnl()) ++ fnl() ++
      str "* " ++ hov 0 (pr_ax csts)));
  end

let stats () =
  print_context (Safe_typing.get_env());
  print_memory_stat ()
