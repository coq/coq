
(* $Id$ *)

open Util

(* Dynamics, programmed with DANGER !!! *)

type t = string * Obj.t

let dyntab = ref ([] : string list)

let create s =
  if List.mem s !dyntab then 
    anomaly ("Dyn.create: already declared dynamic " ^ s);
  dyntab := s :: !dyntab;
  ((fun v -> (s,Obj.repr v)),
   (fun (s',rv) ->
      if s = s' then Obj.magic rv else failwith "dyn_out"))

let tag (s,_) = s
