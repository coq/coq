
(* $Id$ *)

(* Time stamps. *)

type time_stamp = float

let get_time_stamp () = Unix.time()

let compare_time_stamps t1 t2 =
  let dt = t2 -. t1 in
  if dt < 0.0 then -1 else if dt = 0.0 then 0 else 1

