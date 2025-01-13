(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let rec print_list print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list print fmt r

type level = [
  | `DEBUG
  | `INFO
  | `NOTICE
  | `WARNING
  | `ERROR
  | `FATAL ]

(** Some excerpt of Util and similar files to avoid loading the whole
    module and its dependencies (and hence Compat and Camlp5) *)

let debug = ref false

(* On a Win32 application with no console, writing to stderr raise
   a Sys_error "bad file descriptor", hence the "try" below.
   Ideally, we should re-route message to a log file somewhere, or
   print in the response buffer.
*)

let log_pp ?(level = `DEBUG) msg =
  let prefix = match level with
  | `DEBUG -> "DEBUG"
  | `INFO -> "INFO"
  | `NOTICE -> "NOTICE"
  | `WARNING -> "WARNING"
  | `ERROR -> "ERROR"
  | `FATAL -> "FATAL"
  in
  if !debug then begin
    try Format.eprintf "[%s] @[%a@]\n%!" prefix Pp.pp_with msg
    with _ -> ()
  end

let log ?level str = log_pp ?level (Pp.str str)

let rocqify d = Filename.concat d "coq"

let rocqide_config_home () =
  rocqify (Glib.get_user_config_dir ())

let rocqide_data_dirs () =
  rocqify (Glib.get_user_data_dir ())
  :: List.map rocqify (Glib.get_system_data_dirs ())
  @ [Envars.datadir ()]

let rocqide_system_config_dirs () =
  List.map rocqify (Glib.get_system_config_dirs ())

let rocqide_default_config_dir () =
  Envars.configdir ()

let rocqide_config_dirs () =
  rocqide_config_home () ::
  rocqide_system_config_dirs () @
  [rocqide_default_config_dir ()]
