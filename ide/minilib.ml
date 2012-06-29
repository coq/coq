(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
