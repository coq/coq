(* Simple Coq compiler *)

(* Utilities that are common for all toplevels *)
let dirpath_of_file f =
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname f) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let f = try Filename.chop_extension (Filename.basename f) with Invalid_argument _ -> f in
  let id = Names.Id.of_string f in
  let ldir = Libnames.add_dirpath_suffix ldir0 id in
  ldir

let fb_handler = let open Feedback in function
  | Feedback.{ contents; _ } ->
    match contents with
    | Feedback.Message(Debug,_,_) -> ()
    | Feedback.Message(Info,_loc,msg) -> ()
    | Feedback.Message(Notice,_loc,msg)
    | Feedback.Message(Warning,_loc,msg)
    | Feedback.Message(Error,_loc,msg) ->
      Format.printf "%s@\n%!" Pp.(string_of_ppcmds msg)
    | _ -> ()
