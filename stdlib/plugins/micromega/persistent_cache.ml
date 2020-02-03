(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(*  A persistent hashtable                                              *)
(*                                                                      *)
(*  Frédéric Besson (Inria Rennes) 2009-2014                            *)
(*                                                                      *)
(************************************************************************)

module type PHashtable = sig
  (* see documentation in [persistent_cache.mli] *)
  type 'a t
  type key

  val open_in : string -> 'a t
  val find : 'a t -> key -> 'a
  val add : 'a t -> key -> 'a -> unit
  val memo : string -> (key -> 'a) -> key -> 'a
  val memo_cond : string -> (key -> bool) -> (key -> 'a) -> key -> 'a
end

open Hashtbl

module PHashtable (Key : HashedType) : PHashtable with type key = Key.t = struct
  open Unix

  type key = Key.t

  module Table = Hashtbl.Make (Key)

  exception InvalidTableFormat
  exception UnboundTable

  type mode = Closed | Open
  type 'a t = {outch : out_channel; mutable status : mode; htbl : 'a Table.t}

  let finally f rst =
    try
      let res = f () in
      rst (); res
    with reraise ->
      (try rst () with any -> raise reraise);
      raise reraise

  let read_key_elem inch =
    try Some (Marshal.from_channel inch) with
    | End_of_file -> None
    | e when CErrors.noncritical e -> raise InvalidTableFormat

  (**
    We used to only lock/unlock regions.
    Is-it more robust/portable to lock/unlock a fixed region e.g. [0;1]?
    In case of locking failure, the cache is not used.
**)

  type lock_kind = Read | Write

  let lock kd fd =
    let pos = lseek fd 0 SEEK_CUR in
    let success =
      try
        ignore (lseek fd 0 SEEK_SET);
        let lk = match kd with Read -> F_RLOCK | Write -> F_LOCK in
        lockf fd lk 1; true
      with Unix.Unix_error (_, _, _) -> false
    in
    ignore (lseek fd pos SEEK_SET);
    success

  let unlock fd =
    let pos = lseek fd 0 SEEK_CUR in
    try
      ignore (lseek fd 0 SEEK_SET);
      lockf fd F_ULOCK 1
    with Unix.Unix_error (_, _, _) ->
      ()
      (* Here, this is really bad news --
       there is a pending lock which could cause a deadlock.
       Should it be an anomaly or produce a warning ?
    *);
      ignore (lseek fd pos SEEK_SET)

  (* We make the assumption that an acquired lock can always be released *)

  let do_under_lock kd fd f =
    if lock kd fd then finally f (fun () -> unlock fd) else f ()

  let open_in f =
    let flags = [O_RDONLY; O_CREAT] in
    let finch = openfile f flags 0o666 in
    let inch = in_channel_of_descr finch in
    let htbl = Table.create 100 in
    let rec xload () =
      match read_key_elem inch with
      | None -> ()
      | Some (key, elem) -> Table.add htbl key elem; xload ()
    in
    try
      (* Locking of the (whole) file while reading *)
      do_under_lock Read finch xload;
      close_in_noerr inch;
      { outch =
          out_channel_of_descr (openfile f [O_WRONLY; O_APPEND; O_CREAT] 0o666)
      ; status = Open
      ; htbl }
    with InvalidTableFormat ->
      (* The file is corrupted *)
      close_in_noerr inch;
      let flags = [O_WRONLY; O_TRUNC; O_CREAT] in
      let out = openfile f flags 0o666 in
      let outch = out_channel_of_descr out in
      do_under_lock Write out (fun () ->
          Table.iter
            (fun k e -> Marshal.to_channel outch (k, e) [Marshal.No_sharing])
            htbl;
          flush outch);
      {outch; status = Open; htbl}

  let add t k e =
    let {outch; status; htbl = tbl} = t in
    if status == Closed then raise UnboundTable
    else
      let fd = descr_of_out_channel outch in
      Table.add tbl k e;
      do_under_lock Write fd (fun _ ->
          Marshal.to_channel outch (k, e) [Marshal.No_sharing];
          flush outch)

  let find t k =
    let {outch; status; htbl = tbl} = t in
    if status == Closed then raise UnboundTable
    else
      let res = Table.find tbl k in
      res

  let memo cache f =
    let tbl = lazy (try Some (open_in cache) with _ -> None) in
    fun x ->
      match Lazy.force tbl with
      | None -> f x
      | Some tbl -> (
        try find tbl x
        with Not_found ->
          let res = f x in
          add tbl x res; res )

  let memo_cond cache cond f =
    let tbl = lazy (try Some (open_in cache) with _ -> None) in
    fun x ->
      match Lazy.force tbl with
      | None -> f x
      | Some tbl ->
        if cond x then begin
          try find tbl x
          with Not_found ->
            let res = f x in
            add tbl x res; res
        end
        else f x
end

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
