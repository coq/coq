(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let ( / ) s1 s2 = Filename.concat s1 s2

(* Loading of the resource file.
   rcfile is either $XDG_CONFIG_HOME/.coqrc.VERSION, or $XDG_CONFIG_HOME/.coqrc if the first one
  does not exist. *)

let rcdefaultname = "coqrc"

let load_rcfile ~rcfile ~state =
    try
      match rcfile with
      | Some rcfile ->
        if CUnix.file_readable_p rcfile then
          Vernac.load_vernac ~echo:false ~interactive:false ~check:true ~state rcfile
        else raise (Sys_error ("Cannot read rcfile: "^ rcfile))
      | None ->
        try
          let warn x = Feedback.msg_warning (Pp.str x) in
          let inferedrc = List.find CUnix.file_readable_p [
            Envars.xdg_config_home warn / rcdefaultname^"."^Coq_config.version;
            Envars.xdg_config_home warn / rcdefaultname;
            Envars.home ~warn / "."^rcdefaultname^"."^Coq_config.version;
            Envars.home ~warn / "."^rcdefaultname
          ] in
          Vernac.load_vernac ~echo:false ~interactive:false ~check:true ~state inferedrc
        with Not_found -> state
        (*
        Flags.if_verbose
          mSGNL (str ("No coqrc or coqrc."^Coq_config.version^
                         " found. Skipping rcfile loading."))
        *)
    with reraise ->
      let reraise = Exninfo.capture reraise in
      let () = Feedback.msg_info (Pp.str"Load of rcfile failed.") in
      Exninfo.iraise reraise
