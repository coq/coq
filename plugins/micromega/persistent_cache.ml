(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* A persistent hashtable                                               *)
(*                                                                      *)
(*  Frédéric Besson (Inria Rennes) 2009                                 *)
(*                                                                      *)
(************************************************************************)


module type PHashtable = 
  sig
    type 'a t
    type key 

    val create : int -> string -> 'a t
    (** [create i f] creates an empty persistent table 
	with initial size i
	associated with file [f] *)


    val open_in : string -> 'a t
    (** [open_in f] rebuilds a table from the records stored in file [f] *)

    val find : 'a t -> key -> 'a
    (** find has the specification of Hashtable.find *)
      
    val add  : 'a t -> key -> 'a -> unit
    (** [add tbl key elem] adds the binding [key] [elem] to the table [tbl].
	(and writes the binding to the file associated with [tbl].)
	If [key] is already bound, raises KeyAlreadyBound *)

    val close : 'a t -> unit
    (** [close tbl] is closing the table.
	Once closed, a table cannot be used.
	i.e, copy, find,add will raise UnboundTable *)

    val memo : string -> (key -> 'a) -> (key -> 'a)
      (** [memo cache f] returns a memo function for [f] using file [cache] as persistent table.
	  Note that the cache is just loaded when needed *)

  end

open Hashtbl

module PHashtable(Key:HashedType) : PHashtable with type key = Key.t  = 
struct

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
  { 
    outch = open_out_bin f ; 
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


(** [from_file f] returns a hashtable by parsing records from file [f].
    Elements of the file are marshelled pairs of Caml structures.
    (To ensure portability across platforms, closures are not allowed.)

    Raises Sys_error if the file cannot be open
    Raises InvalidTableFormat if the file does not conform to the format
    i.e, Marshal.from_channel fails
*)


let read_key_elem inch =
  try
    Some (Marshal.from_channel inch)
  with 
    | End_of_file -> None
    |    _        -> raise InvalidTableFormat
      
let open_in f = 
  let flags = [Open_rdonly;Open_binary;Open_creat] in
  let inch = open_in_gen flags 0o666 f in
  let htbl = Table.create 10 in

  let rec xload () = 
    match read_key_elem inch with
      | None -> ()
      | Some (key,elem) -> 
	  Table.add htbl key elem ; 
	  xload () in

    try 
      finally (fun () -> xload () ) (fun () -> close_in inch) ;
      {
	outch = begin
	  let flags = [Open_append;Open_binary;Open_creat] in
	    open_out_gen flags 0o666 f 
	end ;
	status = Open ;
	htbl = htbl
      }
    with InvalidTableFormat -> 
      (* Try to keep as many entries as possible *)
      begin
	let flags = [Open_wronly; Open_trunc;Open_binary;Open_creat] in
	let outch = open_out_gen flags 0o666 f in
	  Table.iter (fun k e -> Marshal.to_channel outch (k,e) [Marshal.No_sharing]) htbl; 
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
      begin
	Table.add tbl k e ; 
	Marshal.to_channel outch (k,e) [Marshal.No_sharing]
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
