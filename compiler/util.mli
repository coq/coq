(* Simple Coq compiler *)

(* Utilities that are common for all toplevels *)

val dirpath_of_file : string -> Names.DirPath.t

val fb_handler : Feedback.feedback -> unit
