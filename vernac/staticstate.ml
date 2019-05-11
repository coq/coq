(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* We record the static state of a Coq executable *)

type static_state = {
  coqlib : string;
  compat : Flags.compat_version;
  excluded_dirs : System.unix_path list;
  profile_ltac : bool;
  profile_ltac_cutoff : float;
  record_backtrace : bool;
  tag_map : (string * Terminal.style) list;
  term_color : bool;
  debug : bool;
  warn : bool
}

let freeze_static_state () = {
  coqlib = Envars.coqlib ();
  compat = !Flags.compat_version;
  excluded_dirs = !Minisys.skipped_dirnames;
  profile_ltac = !Flags.profile_ltac;
  profile_ltac_cutoff = !Flags.profile_ltac_cutoff;
  record_backtrace = !Backtrace.is_recording;
  tag_map = Topfmt.dump_tags ();
  term_color = Proof_diffs.color_enabled ();
  debug = !Flags.debug;
  warn = !Flags.warn;
}

let unfreeze_static_state st =
  Envars.set_user_coqlib st.coqlib;
  Flags.compat_version := st.compat;
  Minisys.skipped_dirnames := st.excluded_dirs;
  Flags.profile_ltac := st.profile_ltac;
  Flags.profile_ltac_cutoff := st.profile_ltac_cutoff;
  Backtrace.is_recording := st.record_backtrace;
  Topfmt.init_tag_map st.tag_map;
  Proof_diffs.write_color_enabled st.term_color;
  Flags.debug := st.debug;
  Flags.warn := st.warn;
  ()

(* Do we need to add this:
-topfile ?
-test_mode ?
-async-queries-always-delegate
-async-proofs-always-delegate
-async-proofs-never-reopen-branch

-stm_debug: unaccessible here
*)
