(*
 * hashcons: hash tables for hash consing
 * Copyright (C) 2000 Jean-Christophe FILLIATRE
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

type 'a hash_consed = { 
  hkey : int;
  tag : int;
  node : 'a }

type 'a t = { 
  mutable size : int;                  (* current size *)
  mutable data : 'a bucketlist array } (* the buckets *)

and 'a bucketlist =
  | Empty
  | Cons of 'a hash_consed * 'a bucketlist

let create initial_size =
  let s = if initial_size < 1 then 1 else initial_size in
  let s = if s > Sys.max_array_length then Sys.max_array_length else s in
  { size = 0; data = Array.make s Empty }

let clear h =
  for i = 0 to Array.length h.data - 1 do
    h.data.(i) <- Empty
  done

let resize tbl =
  let odata = tbl.data in
  let osize = Array.length odata in
  let nsize = 2 * osize + 1 in
  let nsize =
    if nsize <= Sys.max_array_length then nsize else Sys.max_array_length
  in
  if nsize <> osize then begin
    let ndata = Array.create nsize Empty in
    let rec insert_bucket = function
	Empty -> ()
      | Cons(data, rest) ->
          insert_bucket rest; (* preserve original order of elements *)
          let nidx = data.hkey mod nsize in
          ndata.(nidx) <- Cons(data, ndata.(nidx)) in
    for i = 0 to osize - 1 do
      insert_bucket odata.(i)
    done;
    tbl.data <- ndata
  end
          
let array_too_small h = Array.length h.data < h.size

let add h hkey info =
  let i = hkey mod (Array.length h.data) in
  let bucket = Cons(info, h.data.(i)) in
  h.data.(i) <- bucket;
  h.size <- h.size + 1;
  if array_too_small h then resize h

let find h key hkey =
  match h.data.(hkey mod (Array.length h.data)) with
    Empty -> raise Not_found
  | Cons(d1, rest1) ->
      if key = d1.node then d1 else
      match rest1 with
        Empty -> raise Not_found
      | Cons(d2, rest2) ->
          if key = d2.node then d2 else
          match rest2 with
            Empty -> raise Not_found
          | Cons(d3, rest3) ->
              if key = d3.node then d3 else begin
                let rec find = function
                    Empty ->
                      raise Not_found
                  | Cons(d, rest) ->
                      if key = d.node then d else find rest
                in find rest3
              end

let gentag =
  let r = ref 0 in
  fun () -> incr r; !r

let hashcons h node =
  let hkey = Hashtbl.hash_param 10 100 node in
  try 
    find h node hkey
  with Not_found -> 
    let hnode = { hkey = hkey; tag = gentag(); node = node } in
    add h hkey hnode;
    hnode

let iter f h =
  let rec bucket_iter = function
    | Empty -> ()
    | Cons (x,l) -> f x; bucket_iter l
  in
  Array.iter bucket_iter h.data

let rec bucketlist_length = function
  | Empty -> 0
  | Cons (_,bl) -> succ (bucketlist_length bl)

let stat h =
  let d = h.data in
  let size = Array.length d in
  let ne = ref 0 in
  let m = ref 0 in
  let t = ref 0 in
  for i = 0 to size - 1 do
    let n = bucketlist_length d.(i) in
    t := !t + n;
    if n > 0 then incr ne;
    if n > !m then m := n
  done;
  let p = 100 * !ne / size in
  Printf.printf 
    "%6d val, used = %6d / %6d (%2d%%), max length = %6d\n" 
    !t !ne size p !m

(* Functorial interface *)

module type HashedType =
  sig
    type t
    val equal : t * t -> bool
    val hash : t -> int
  end

module type S =
  sig
    type key
    type t
    val create : int -> t
    val clear : t -> unit
    val hashcons : t -> key -> key hash_consed
    val iter : (key hash_consed -> unit) -> t -> unit
    val stat : t -> unit
  end

module Make(H : HashedType) : (S with type key = H.t) =
  struct
    type key = H.t
    type hashtbl = key t
    type t = hashtbl

    let create = create
    let clear = clear
    
    let add h hkey info =
      let i = hkey mod (Array.length h.data) in
      let bucket = Cons(info, h.data.(i)) in
      begin
	h.data.(i) <- bucket;
	h.size <- h.size + 1;
	if array_too_small h then resize h;
	(*
	if h.size mod 1000 = 0 then
	  begin
	    Printf.printf "hkey = %d, i = %d\n" hkey i;
	    stat h;
	    flush stdout
	  end
	  *)
      end

    let find h key hkey =
      match h.data.(hkey mod (Array.length h.data)) with
        Empty -> raise Not_found
      | Cons(d1, rest1) ->
          if H.equal (key, d1.node) then d1 else
          match rest1 with
            Empty -> raise Not_found
          | Cons(d2, rest2) ->
              if H.equal (key, d2.node) then d2 else
              match rest2 with
                Empty -> raise Not_found
              | Cons(d3, rest3) ->
                  if H.equal (key, d3.node) then d3 else begin
                    let rec find = function
                        Empty ->
                          raise Not_found
                      | Cons(d, rest) ->
                          if H.equal (key, d.node) then d else find rest
                    in find rest3
                  end

    let hashcons h node =
      let hkey = H.hash node in
      try 
	find h node hkey
      with Not_found -> 
	let hnode = { hkey = hkey; tag = gentag(); node = node } in
	add h hkey hnode;
	hnode

    let iter = iter

    let stat = stat
  end
