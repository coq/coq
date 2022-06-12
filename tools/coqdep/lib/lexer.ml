(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* XXX *)
open Gramlib

let of_list l =
  let rl = ref l in
  Stream.from (fun () ->
      match !rl with
      | [] -> None
      | x :: xs -> rl := xs; Some x)

(* Interface to coqmod's lexer *)
type qualid = string list

type load = Logical of string | Physical of string

type coq_token =
  | Require of qualid option * qualid list
  | Declare of string list
  | Load of load
  | External of qualid * string

exception Fin_fichier
exception Syntax_error of int*int

module CM = Coqmodlib
module CT = Coqmodlib.Token

let rec read_buffer t buf =
  match CM.Lexer.parse_coq t buf with
  | t -> read_buffer t buf
  | exception CM.Lexer.End_of_file -> t

type t = coq_token Stream.t

let parse_mod = String.split_on_char '.'

let of_froms CT.From.{ prefix; require } =
  let from = Option.map (fun p -> parse_mod p.CT.Module.logical_name) prefix in
  Require (from, [parse_mod require.CT.Module.logical_name])

let of_declares CT.Module.{logical_name} =
  Declare [logical_name]

let of_loads CT.Load.{path} =
  Load (Physical path)

let of_extradeps CT.ExtraDep.{ from; file } =
  External (parse_mod from.CT.Module.logical_name, file)

let to_list (lr : CT.t) : coq_token list =
  let CT.{ filename = _; froms; declares; loads; extradeps } = lr in
  let m = List.map in
  m of_froms froms @ m of_declares declares @ m of_loads loads @ m of_extradeps extradeps

let stream_tokens lr = to_list lr |> of_list

let lex_coq ~file buf =
  let tok = CM.Token.set_filename CM.Token.empty file in
  read_buffer tok buf |> stream_tokens

let next_token str =
  match Stream.peek str with
  | None -> raise Fin_fichier
  | Some x -> Stream.next str
