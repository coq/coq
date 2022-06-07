(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let debug_mode = ref false

exception CannotOpenFile of string * string

exception UnknownOutputFormat of string

exception NoFileProvided

exception TooManyFilesProvided

let _ =
  CErrors.register_handler
  @@ function
  | CannotOpenFile (s, msg) -> Some Pp.(str s ++ str ":" ++ spc () ++ str msg)
  | UnknownOutputFormat format ->
      Some Pp.(strbrk "Error: Unkown output format: " ++ str format)
  | NoFileProvided ->
      Some Pp.(strbrk "Error: No file provided. Please provide a file.")
  | TooManyFilesProvided ->
      Some
        Pp.(
          strbrk
            "Error: Too many files provided. Please provide only a single file.")
  | _ -> None

let cannot_open s msg = raise @@ CannotOpenFile (s, msg)

let unknwon_output_format format = raise @@ UnknownOutputFormat format

let no_file_provided () = raise @@ NoFileProvided

let too_many_files_provided () = raise @@ TooManyFilesProvided
