(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
let debug : (string, int) Hashtbl.t = Hashtbl.create 97

let create ~name =
  if CString.equal name "all" then CErrors.user_err Pp.(str"The name \"all\" is reserved.");
  let pp x =
    Feedback.msg_debug Pp.(str "[" ++ str name ++ str "] " ++ x)
  in
  let default_level = if !Flags.debug then 1 else 0 in
  Hashtbl.add debug name default_level;
  fun ?(verbosity = 2) x -> if Hashtbl.find debug name >= verbosity then pp (x ())

let set_debug_level (name,verbosity) =
  if CString.equal name "all" then
    Hashtbl.filter_map_inplace (fun _ _ -> Some verbosity) debug
  else
    Hashtbl.replace debug name verbosity

let get_debug_level name =
  Option.default 0 (Hashtbl.find_opt debug name)

let set_debug_levels flags =
  List.iter set_debug_level flags

let get_flags () =
  let flags = Hashtbl.fold (fun name v acc -> (name ^ "=" ^ string_of_int v) :: acc) debug [] in
  String.concat "," flags

let parse_flags s =
  let parse_flag s =
    match String.split_on_char '=' s with
    | [x;y] -> (x,int_of_string y)
    | _ -> raise (Failure "parse_flags")
  in
  try
    Some (List.map parse_flag @@ String.split_on_char ',' s)
  with Failure _ -> None
