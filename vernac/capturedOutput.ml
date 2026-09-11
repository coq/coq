(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* NB we could also keep the loc but it's unstable between coqtop
   (proof general) and files so hard to use.Q

   Could also add phase info, not sure if useful. *)
type output = Message of Feedback.level * Pp.t

type t = output list

let from_rev_list l = List.rev l

let from_list l = l

type flags = {
  width : int option;
}

let default_flags = {
  width = None;
}

let parse_flag acc (flag : Vernacexpr.AssertCapturedOutputFlags.t CAst.t) =
  match flag.v with
  (* NoDrop handled outside this file *)
  | NoDrop -> acc
  | PrintingWidth w ->
    if Option.has_some acc.width then
      CErrors.user_err ?loc:flag.loc Pp.(str "Duplicate flag " ++ Ppvernac.pr_assert_captured_output_flag flag.v ++ str ".")
    else { width = Some w }

let parse_flags flags = List.fold_left parse_flag default_flags flags

let buf = Buffer.create 117

let pp_with_width w out =
  let fmt = Format.formatter_of_buffer buf in
  Topfmt.set_gp fmt { Topfmt.dflt_gp with margin = w };
  Pp.pp_with fmt out;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let pp_with_width w out =
  Util.try_finally (fun () -> pp_with_width w out) ()
    (fun () -> Buffer.reset buf) ()

let print_captured_with_width w out =
  let print_one (Message (_, msg)) = pp_with_width w msg in
  let out = List.map print_one out in
  String.concat "\n" out

exception Mismatch of Loc.t option * string

let () = CErrors.register_handler @@ function
  | Mismatch (_,s) -> Some Pp.(str "Not OK: expected" ++ spc() ++ qstring s)
  | _ -> None

let () = Quickfix.register @@ function
  | Mismatch (Some loc,s) -> [Quickfix.make ~loc (Pp.qstring s)]
  | _ -> []

let vernac_assert out flags {CAst.loc; v=s} =
  let flags = parse_flags flags in
  match flags.width with
  | None -> CErrors.user_err Pp.(str "Explicit printing width required.")
  | Some w ->
    let out =
      print_captured_with_width
        (Option.default (Option.get @@ Topfmt.get_margin()) flags.width)
        out
    in
    (* XXX trim? (remove whitespace at end of lines, remove empty line at begin/end) *)
    if String.equal out s then Feedback.msg_info ?loc Pp.(str "Output OK.")
    else
      (* XXX make this an error by default warning so that it's easy
         to see all output mismatch from a file? *)
      (* TODO print in patch format? *)
      Loc.raise ?loc (Mismatch (loc,out))
