(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*         Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt       *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type ('e,'a) t = { mutable count : int; mutable data : ('e,'a) data }
and ('e,'a) data =
    Sempty
  | Scons of 'a * ('e,'a) data
  | Sgen of ('e,'a) gen
  | Sbuffio : buffio -> (unit,char) data
and ('e,'a) gen = { mutable curr : 'a option option; func : 'e -> 'a option }
and buffio =
  { ic : in_channel; buff : bytes; mutable len : int; mutable ind : int }

exception Failure

let count { count } = count

let fill_buff b =
  b.len <- input b.ic b.buff 0 (Bytes.length b.buff); b.ind <- 0

let peek : type e v. e -> (e,v) t -> v option = fun e s ->
 (* consult the first item of s *)
 match s.data with
   Sempty -> None
 | Scons (a, _) -> Some a
 | Sgen {curr = Some a} -> a
 | Sgen g -> let x = g.func e in g.curr <- Some x; x
 | Sbuffio b ->
     if b.ind >= b.len then fill_buff b;
     if b.len == 0 then begin s.data <- Sempty; None end
     else Some (Bytes.unsafe_get b.buff b.ind)


let rec junk : type e v. e -> (e,v) t -> unit = fun e s ->
  match s.data with
    Scons (_, d) -> s.count <- (succ s.count); s.data <- d
  | Sgen ({curr = Some _} as g) -> s.count <- (succ s.count); g.curr <- None
  | Sbuffio b ->
      if b.ind >= b.len then fill_buff b;
      if b.len == 0 then s.data <- Sempty
      else (s.count <- (succ s.count); b.ind <- succ b.ind)
  | Sempty -> ()
  | Sgen { curr = None } ->
      match peek e s with
        None -> ()
      | Some _ -> junk e s

let rec nget e n s =
  if n <= 0 then [], s.data, 0
  else
    match peek e s with
      Some a ->
        junk e s;
        let (al, d, k) = nget e (pred n) s in a :: al, Scons (a, d), succ k
    | None -> [], s.data, 0


let npeek e n s =
  let (al, d, len) = nget e n s in
  s.count <- (s.count - len);
  s.data <- d;
  al

let nth e n st =
  try List.nth (npeek e (n+1) st) n
  with Stdlib.Failure _ -> raise Failure

let rec njunk e n st =
  if n <> 0 then (junk e st; njunk e (n-1) st)

let next e s =
  match peek e s with
    Some a -> junk e s; a
  | None -> raise Failure


let is_empty e s =
  match peek e s with
  | Some _ -> false
  | None -> true


(* Stream building functions *)

let from ?(offset=0) f = {count = offset; data = Sgen {curr = None; func = f}}

(* NB we need the thunk for value restriction *)
let empty () = {count = 0; data = Sempty}

let of_string ?(offset=0) s =
  let count = ref 0 in
  from ~offset (fun () ->
    let c = !count in
    if c < String.length s
    then (incr count; Some s.[c])
    else None)


let of_channel ic =
  {count = 0;
        data = Sbuffio {ic = ic; buff = Bytes.create 4096; len = 0; ind = 0}}
