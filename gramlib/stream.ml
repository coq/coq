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

type 'a t = 'a cell option
and 'a cell = { mutable count : int; mutable data : 'a data }
and 'a data =
    Sempty
  | Scons of 'a * 'a data
  | Sapp of 'a data * 'a data
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

let count = function
  | None -> 0
  | Some { count } -> count
let data = function
  | None -> Sempty
  | Some { data } -> data

let fill_buff b =
  b.len <- input b.ic b.buff 0 (Bytes.length b.buff); b.ind <- 0


let rec get_data : type v. v data -> v data = fun d -> match d with
 (* Returns either Sempty or Scons(a, _) even when d is a generator
    or a buffer. In those cases, the item a is seen as extracted from
 the generator/buffer.
 The count parameter is used for calling `Sgen-functions'.  *)
   Sempty | Scons (_, _) -> d
 | Sapp (d1, d2) ->
     begin match get_data d1 with
       Scons (a, d11) -> Scons (a, Sapp (d11, d2))
     | Sempty -> get_data d2
     | _ -> assert false
     end
 | Sgen {curr = Some None} -> Sempty
 | Sgen ({curr = Some(Some a)} as g) ->
     g.curr <- None; Scons(a, d)
 | Sgen g ->
     begin match g.func () with
       None -> g.curr <- Some(None); Sempty
     | Some a -> Scons(a, d)
         (* Warning: anyone using g thinks that an item has been read *)
     end
 | Sbuffio b ->
     if b.ind >= b.len then fill_buff b;
     if b.len == 0 then Sempty else
       let r = Bytes.unsafe_get b.buff b.ind in
       (* Warning: anyone using g thinks that an item has been read *)
       b.ind <- succ b.ind; Scons(r, d)


let peek_data : type v. v cell -> v option = fun s ->
 (* consult the first item of s *)
 match s.data with
   Sempty -> None
 | Scons (a, _) -> Some a
 | Sapp (_, _) ->
     begin match get_data s.data with
       Scons(a, _) as d -> s.data <- d; Some a
     | Sempty -> None
     | _ -> assert false
     end
 | Sgen {curr = Some a} -> a
 | Sgen g -> let x = g.func () in g.curr <- Some x; x
 | Sbuffio b ->
     if b.ind >= b.len then fill_buff b;
     if b.len == 0 then begin s.data <- Sempty; None end
     else Some (Bytes.unsafe_get b.buff b.ind)


let peek = function
  | None -> None
  | Some s -> peek_data s


let rec junk_data : type v. v cell -> unit = fun s ->
  match s.data with
    Scons (_, d) -> s.count <- (succ s.count); s.data <- d
  | Sgen ({curr = Some _} as g) -> s.count <- (succ s.count); g.curr <- None
  | Sbuffio b ->
      if b.ind >= b.len then fill_buff b;
      if b.len == 0 then s.data <- Sempty
      else (s.count <- (succ s.count); b.ind <- succ b.ind)
  | _ ->
      match peek_data s with
        None -> ()
      | Some _ -> junk_data s


let junk = function
  | None -> ()
  | Some data -> junk_data data

let rec nget_data n s =
  if n <= 0 then [], s.data, 0
  else
    match peek_data s with
      Some a ->
        junk_data s;
        let (al, d, k) = nget_data (pred n) s in a :: al, Scons (a, d), succ k
    | None -> [], s.data, 0


let npeek_data n s =
  let (al, d, len) = nget_data n s in
  s.count <- (s.count - len);
  s.data <- d;
  al


let npeek n = function
  | None -> []
  | Some d -> npeek_data n d

let nth n st =
  try List.nth (npeek (n+1) st) n
  with Stdlib.Failure _ -> raise Failure

let rec njunk n st =
  if n <> 0 then (junk st; njunk (n-1) st)

let next s =
  match peek s with
    Some a -> junk s; a
  | None -> raise Failure


let empty s =
  match peek s with
    Some _ -> raise Failure
  | None -> ()


(* Stream building functions *)

let from f = Some {count = 0; data = Sgen {curr = None; func = f}}

let of_list l =
  Some {count = 0; data = List.fold_right (fun x l -> Scons (x, l)) l Sempty}


let of_string s =
  let count = ref 0 in
  from (fun () ->
    let c = !count in
    if c < String.length s
    then (incr count; Some s.[c])
    else None)


let of_channel ic =
  Some {count = 0;
        data = Sbuffio {ic = ic; buff = Bytes.create 4096; len = 0; ind = 0}}

(* For debugging use *)

let rec dump : type v. (v -> unit) -> v t -> unit = fun f s ->
  print_string "{count = ";
  print_int (count s);
  print_string "; data = ";
  dump_data f (data s);
  print_string "}";
  print_newline ()
and dump_data : type v. (v -> unit) -> v data -> unit = fun f ->
  function
    Sempty -> print_string "Sempty"
  | Scons (a, d) ->
      print_string "Scons (";
      f a;
      print_string ", ";
      dump_data f d;
      print_string ")"
  | Sapp (d1, d2) ->
      print_string "Sapp (";
      dump_data f d1;
      print_string ", ";
      dump_data f d2;
      print_string ")"
  | Sgen _ -> print_string "Sgen"
  | Sbuffio _ -> print_string "Sbuffio"
