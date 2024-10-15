(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type flag = bool ref

type t = (unit -> Pp.t) -> unit

let debug = ref CString.Map.empty

(* Used to remember level of Set Debug "all" for debugs created by
   plugins dynlinked after the Set *)
let all_flag = ref false

let set_debug_backtrace b =
  Exninfo.record_backtrace b

let set_debug_all b =
  set_debug_backtrace b;
  CString.Map.iter (fun _ flag -> flag := b) !debug;
  all_flag := b

let create_full ~name () =
  let anomaly pp = CErrors.anomaly ~label:"CDebug.create" pp in
  let () = match name with
    | "all"|"backtrace" -> anomaly Pp.(str"The debug name \""++str name++str"\" is reserved.")
    | _ ->
      if CString.Map.mem name !debug then
        anomaly Pp.(str "The debug name \"" ++ str name ++ str "\" is already used.")
  in
  let pp x =
    Feedback.msg_debug Pp.(hv 2 (str "[" ++ str name ++ str "]" ++ spc() ++ x))
  in
  let flag = ref !all_flag in
  debug := CString.Map.add name flag !debug;
  let pp x =
    if !flag
    then pp (x ())
  in
  flag, pp

let create ~name () =
  snd (create_full ~name ())

let get_flag flag = !flag

let set_flag flag v = flag := v

let warn_unknown_debug = CWarnings.create ~name:"unknown-debug-flag"
    Pp.(fun name -> str "There is no debug flag \"" ++ str name ++ str "\".")

let get_flags () =
  let pp_flag name flag = if flag then name else "-"^name in
  let flags =
    CString.Map.fold
      (fun name v acc -> pp_flag name !v :: acc)
      !debug []
  in
  let all = pp_flag "all" !all_flag in
  let bt = pp_flag "backtrace" (Printexc.backtrace_status()) in
  String.concat "," (all::bt::flags)

exception Error

let parse_flags s =
  let parse_flag s =
    if CString.is_empty s then raise Error
    else if s.[0] = '-'
    then String.sub s 1 (String.length s - 1), false
    else s, true
  in
  try
    Some (CList.map parse_flag @@ String.split_on_char ',' s)
  with Error -> None

let set_flags s = match parse_flags s with
  | None -> CErrors.user_err Pp.(str "Syntax error in debug flags.")
  | Some flags ->
    let set_one_flag (name,b) = match name with
      | "all" -> set_debug_all b
      | "backtrace" -> set_debug_backtrace b
      | _ -> match CString.Map.find_opt name !debug with
        | None -> warn_unknown_debug name
        | Some flag -> flag := b
    in
    List.iter set_one_flag flags

let misc, pp_misc = create_full ~name:"misc" ()
