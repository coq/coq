(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
    module and its dependencies (and hence Compat and Camlp4) *)

let debug = ref false

(* On a Win32 application with no console, writing to stderr raise
   a Sys_error "bad file descriptor", hence the "try" below.
   Ideally, we should re-route message to a log file somewhere, or
   print in the response buffer.
*)

let log ?(level = `DEBUG) msg =
  let prefix = match level with
  | `DEBUG -> "DEBUG"
  | `INFO -> "INFO"
  | `NOTICE -> "NOTICE"
  | `WARNING -> "WARNING"
  | `ERROR -> "ERROR"
  | `FATAL -> "FATAL"
  in
  if !debug then begin
    try Printf.eprintf "[%s] %s\n%!" prefix msg
    with _ -> ()
  end

let coqify d = Filename.concat d "coq"

let coqide_config_home () =
  coqify (Glib.get_user_config_dir ())

let coqide_data_dirs () =
  coqify (Glib.get_user_data_dir ())
  :: List.map coqify (Glib.get_system_data_dirs ())
  @ Option.List.cons Coq_config.datadir []

let coqide_config_dirs () =
  coqide_config_home ()
  :: List.map coqify (Glib.get_system_config_dirs ())
  @ Option.List.cons Coq_config.configdir []

let is_prefix_of pre s =
  let i = ref 0 in
  let () = while (!i < (String.length pre)
        && !i < (String.length s)
	     && pre.[!i] = s.[!i]) do
	          incr i
		     done
  in !i = String.length pre

