(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [`ON | `AUTO | `EMACS | `OFF]

let init_color opts =
  let has_color = match opts with
  | `OFF -> false
  | `EMACS -> false
  | `ON -> true
  | `AUTO ->
    Terminal.has_style Unix.stdout &&
    Terminal.has_style Unix.stderr &&
    (* emacs compilation buffer does not support colors by default,
       its TERM variable is set to "dumb". *)
    try Sys.getenv "TERM" <> "dumb" with Not_found -> false
  in
  let term_color =
    if has_color then begin
      match Envars.getenv_rocq "_COLORS" with
      | None -> Topfmt.default_styles (); true        (* Default colors *)
      | Some "" -> false                              (* No color output *)
      | Some s -> Topfmt.parse_color_config s; true   (* Overwrite all colors *)
    end
    else begin
      Topfmt.default_styles (); false                 (* textual markers, no color *)
    end
  in
  if opts = `EMACS then
    Topfmt.set_emacs_print_strings ()
  else if not term_color then begin
      Proof_diffs.write_color_enabled term_color;
    if Proof_diffs.show_diffs () then
      (prerr_endline "Error: -diffs requires enabling -color"; exit 1)
  end;
  Topfmt.init_terminal_output ~color:term_color

let print_style_tags opts =
  let () = init_color opts in
  let tags = Topfmt.dump_tags () in
  let iter (t, st) =
    let opt = Terminal.eval st ^ t ^ Terminal.reset ^ "\n" in
    print_string opt
  in
  let make (t, st) =
    let tags = List.map string_of_int (Terminal.repr st) in
    (t ^ "=" ^ String.concat ";" tags)
  in
  let repr = List.map make tags in
  let () = Printf.printf "ROCQ_COLORS=\"%s\"\n" (String.concat ":" repr) in
  let () = List.iter iter tags in
  flush_all ()


let set_color = function
  | "yes" | "on" -> `ON
  | "no" | "off" -> `OFF
  | "auto" ->`AUTO
  | _ ->
    Coqargs.error_wrong_arg ("Error: on/off/auto expected after option color")


let parse_extra_colors ~emacs extras =
  let rec parse_extra color_mode = function
  | "-color" :: next :: rest -> parse_extra (set_color next) rest
  | x :: rest ->
    let color_mode, rest = parse_extra color_mode rest in color_mode, x :: rest
  | [] -> color_mode, [] in
  let c, extras = parse_extra `AUTO extras in
  (* we parse -color but ignore it when -emacs
     maybe should be the other way (ignore -emacs for color printing if -color is given)? *)
  let c = if emacs then `EMACS else c in
  c, extras
