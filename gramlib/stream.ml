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

type 'a t = { mutable count : int; mutable data : 'a data }
and 'a data =
    Sempty
  | Scons of 'a * 'a data
  | Sgen of 'a gen
  | Sbuffio : buffio -> char data
and 'a gen = { mutable curr : 'a option option; func : unit -> 'a option }
and buffio =
  { ic : in_channel; buff : bytes; mutable len : int; mutable ind : int }

(* We use exception Foo = Stdlib.Stream.Foo to make it easier for
   plugins since they won't be getting type errors when using them. *)

exception Failure = Stdlib.Stream.Failure
[@@ocaml.warning "-3"]

exception Error = Stdlib.Stream.Error
[@@ocaml.warning "-3"]

let count { count } = count

let fill_buff b =
  b.len <- input b.ic b.buff 0 (Bytes.length b.buff); b.ind <- 0

let peek : type v. v t -> v option = fun s ->
 (* consult the first item of s *)
 match s.data with
   Sempty -> None
 | Scons (a, _) -> Some a
 | Sgen {curr = Some a} -> a
 | Sgen g -> let x = g.func () in g.curr <- Some x; x
 | Sbuffio b ->
     if b.ind >= b.len then fill_buff b;
     if b.len == 0 then begin s.data <- Sempty; None end
     else Some (Bytes.unsafe_get b.buff b.ind)


let rec junk : type v. v t -> unit = fun s ->
  match s.data with
    Scons (_, d) -> s.count <- (succ s.count); s.data <- d
  | Sgen ({curr = Some _} as g) -> s.count <- (succ s.count); g.curr <- None
  | Sbuffio b ->
      if b.ind >= b.len then fill_buff b;
      if b.len == 0 then s.data <- Sempty
      else (s.count <- (succ s.count); b.ind <- succ b.ind)
  | _ ->
      match peek s with
        None -> ()
      | Some _ -> junk s

let rec nget n s =
  if n <= 0 then [], s.data, 0
  else
    match peek s with
      Some a ->
        junk s;
        let (al, d, k) = nget (pred n) s in a :: al, Scons (a, d), succ k
    | None -> [], s.data, 0


let npeek n s =
  let (al, d, len) = nget n s in
  s.count <- (s.count - len);
  s.data <- d;
  al

let nth n st =
  try List.nth (npeek (n+1) st) n
  with Stdlib.Failure _ -> raise Failure

let rec njunk n st =
  if n <> 0 then (junk st; njunk (n-1) st)

let next s =
  match peek s with
    Some a -> junk s; a
  | None -> raise Failure


let is_empty s =
  match peek s with
  | Some _ -> false
  | None -> true


(* Stream building functions *)

let from f = {count = 0; data = Sgen {curr = None; func = f}}

let of_list l =
  {count = 0; data = List.fold_right (fun x l -> Scons (x, l)) l Sempty}


let of_string s =
  let count = ref 0 in
  from (fun () ->
    let c = !count in
    if c < String.length s
    then (incr count; Some s.[c])
    else None)


let of_channel ic =
  {count = 0;
        data = Sbuffio {ic = ic; buff = Bytes.create 4096; len = 0; ind = 0}}
