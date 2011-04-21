(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(*  A persistent hashtable                                              *)
(*                                                                      *)
(*  Frédéric Besson (Inria Rennes) 2009-2011                            *)
(*                                                                      *)
(************************************************************************)


module type PHashtable =
  sig
    type 'a t
    type key

    val create : int -> string -> 'a t
    (** [create i f] creates an empty persistent table
	with initial size i associated with file [f] *)


    val open_in : string -> 'a t
    (** [open_in f] rebuilds a table from the records stored in file [f].
	As marshaling is not type-safe, it migth segault.
    *)

    val find : 'a t -> key -> 'a
    (** find has the specification of Hashtable.find *)

    val add  : 'a t -> key -> 'a -> unit
    (** [add tbl key elem] adds the binding [key] [elem] to the table [tbl].
	(and writes the binding to the file associated with [tbl].)
	If [key] is already bound, raises KeyAlreadyBound *)

    val close : 'a t -> unit
    (** [close tbl] is closing the table.
	Once closed, a table cannot be used.
	i.e, find,add will raise UnboundTable *)

    val memo : string -> (key -> 'a) -> (key -> 'a)
      (** [memo cache f] returns a memo function for [f] using file [cache] as persistent table.
	  Note that the cache will only be loaded when the function is used for the first time *)

  end

open Hashtbl

module PHashtable(Key:HashedType) : PHashtable with type key = Key.t  =
struct
  open Unix

  type key = Key.t

  module Table = Hashtbl.Make(Key)

  exception InvalidTableFormat
  exception UnboundTable

  type mode = Closed | Open

  type 'a t =
      {
	outch : out_channel ;
	mutable status : mode ;
	htbl : 'a Table.t
      }


let create i f =
  let flags = [O_WRONLY; O_TRUNC;O_CREAT] in
  {
    outch = out_channel_of_descr (openfile f flags 0o666);
    status = Open ;
    htbl = Table.create i
  }

let finally f rst =
  try
    let res = f () in
      rst () ; res
  with x ->
    (try rst ()
    with _  -> raise x
    ); raise x


let read_key_elem inch =
  try
    Some (Marshal.from_channel inch)
  with
    | End_of_file -> None
    |    _        -> raise InvalidTableFormat


let unlock fd = 
  try 
    let pos = lseek fd 0 SEEK_CUR in
    ignore (lseek fd 0 SEEK_SET) ; 
    lockf fd F_ULOCK 0 ; 
  ignore (lseek fd pos SEEK_SET)
  with exc -> failwith (Printexc.to_string exc)

let open_in f =
  let flags = [O_RDONLY ; O_CREAT] in
  let finch = openfile f flags 0o666 in
  let inch  = in_channel_of_descr finch in
  let htbl = Table.create 100 in

  let rec xload () =
    match read_key_elem inch with
      | None -> ()
      | Some (key,elem) ->
	  Table.add htbl key elem ;
	  xload () in
    try
      (* Locking of the (whole) file while reading *)
      lockf finch F_RLOCK 0 ; 
      finally 
	(fun () -> xload () ) 
	(fun () -> 
	   unlock finch ;
	   close_in_noerr inch ; 
	) ;
      {
	outch = out_channel_of_descr (openfile f [O_WRONLY;O_APPEND;O_CREAT] 0o666) ;
	status = Open ;
	htbl = htbl
      }
    with InvalidTableFormat ->
      (* Try to keep as many entries as possible *)
      begin
	let flags = [O_WRONLY; O_TRUNC;O_CREAT] in
	let out =  (openfile f flags 0o666) in
	let outch = out_channel_of_descr out in
	  lockf out F_LOCK 0 ; 
	  (try 
	    Table.iter 
	      (fun k e -> Marshal.to_channel outch (k,e) [Marshal.No_sharing]) htbl;
	    flush outch ; 
	  with  _ -> () )
	    ;
	    unlock out ; 
	    { outch = outch ;
	      status = Open ;
	      htbl   = htbl
	    }
      end


let close t =
  let {outch = outch ; status = status ; htbl = tbl} = t in
    match t.status with
    | Closed -> () (* don't do it twice *)
    | Open  ->
	close_out outch ;
	Table.clear tbl ;
	t.status <- Closed

let add t k e =
  let {outch = outch ; status = status ; htbl = tbl} = t in
    if status = Closed
    then raise UnboundTable
    else
      let fd = descr_of_out_channel outch in
      begin
	Table.add tbl k e ;
	lockf fd F_LOCK 0 ;
	ignore (lseek fd 0 SEEK_END) ; 
	Marshal.to_channel outch (k,e) [Marshal.No_sharing] ;
	flush outch ;
	unlock fd
      end

let find t k =
  let {outch = outch ; status = status ; htbl = tbl} = t in
    if status = Closed
    then raise UnboundTable
    else
      let res = Table.find tbl k in
	res

let memo cache f =
  let tbl = lazy (open_in cache) in
    fun x ->
      let tbl = Lazy.force tbl in
	try
	  find tbl x
	with
	    Not_found ->
	      let res = f x in
		add tbl x res ;
		res

end


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
