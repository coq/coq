open Lwt.Infix

let fatal_plumbing_error = function
  | End_of_file ->
      Printf.eprintf "link closed, goodbye!\n%!";
      exit 0
  | Lwt_io.Channel_closed s ->
      CErrors.anomaly Pp.(str "Lwt channel used after close: " ++ str s)
  | Unix.Unix_error (e,fname,farg) ->
      Printf.eprintf "%s %s: %s\n%!" fname farg (Unix.error_message e);
      exit 1
  | exn ->
      Printf.eprintf "Unknown exception: %s\n%!" (Printexc.to_string exn);
      exit 2

module Infix = struct

(** reify exception *)
let (>?=) p q =
  Lwt_result.catch p >>= q

(** assert *)
let (>!=) p q =
  p >?= function
    | Result.Ok v -> q v
    | Result.Error exn -> fatal_plumbing_error exn

end