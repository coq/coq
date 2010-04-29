(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This module manages customization parameters at the vernacular level     *)

open Pp
open Util
open Libobject
open Names
open Libnames
open Term
open Nametab
open Mod_subst

(****************************************************************************)
(* 0- Common things                                                         *)

type option_name = string list

let nickname table = String.concat " " table

let error_undeclared_key key =
  error ((nickname key)^": no table or option of this type")

type value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | IdentValue  of global_reference

(****************************************************************************)
(* 1- Tables                                                                *)

class type ['a] table_of_A =
object
  method add : 'a -> unit
  method remove : 'a -> unit
  method mem : 'a -> unit
  method print : unit
end

module MakeTable =
  functor
   (A : sig
	  type t
	  type key
	  val table : (string * key table_of_A) list ref
	  val encode : key -> t
	  val subst : substitution -> t -> t
          val printer : t -> std_ppcmds
          val key : option_name
          val title : string
          val member_message : t -> bool -> std_ppcmds
          val synchronous : bool
        end) ->
  struct
    type option_mark =
      | GOadd
      | GOrmv

    let nick = nickname A.key

    let _ =
      if List.mem_assoc nick !A.table then
	error "Sorry, this table name is already used"

    module MySet = Set.Make (struct type t = A.t let compare = compare end)

    let t = ref (MySet.empty : MySet.t)

    let _ =
      if A.synchronous then
	let freeze () = !t in
	let unfreeze c = t := c in
	let init () = t := MySet.empty in
	Summary.declare_summary nick
          { Summary.freeze_function = freeze;
            Summary.unfreeze_function = unfreeze;
            Summary.init_function = init }

    let (add_option,remove_option) =
      if A.synchronous then
        let cache_options (_,(f,p)) = match f with
          | GOadd -> t := MySet.add p !t
          | GOrmv -> t := MySet.remove p !t in
        let load_options i o = if i=1 then cache_options o in
	let subst_options (subst,(f,p as obj)) = 
	  let p' = A.subst subst p in
	    if p' == p then obj else
	      (f,p')
	in
        let (inGo,outGo) =
          Libobject.declare_object {(Libobject.default_object nick) with
                Libobject.load_function = load_options;
		Libobject.open_function = load_options;
		Libobject.cache_function = cache_options;
		Libobject.subst_function = subst_options;
		Libobject.classify_function = (fun x -> Substitute x)}
	in
        ((fun c -> Lib.add_anonymous_leaf (inGo (GOadd, c))),
         (fun c -> Lib.add_anonymous_leaf (inGo (GOrmv, c))))
      else
        ((fun c -> t := MySet.add c !t),
         (fun c -> t := MySet.remove c !t))

    let print_table table_name printer table =
      msg (str table_name ++
	   (hov 0
	      (if MySet.is_empty table then str "None" ++ fnl ()
               else MySet.fold
		 (fun a b -> printer a ++ spc () ++ b)
		 table (mt ()) ++ fnl ())))

    class table_of_A () =
    object
      method add x = add_option (A.encode x)
      method remove x = remove_option (A.encode x)
      method mem x =
	let y = A.encode x in
        let answer = MySet.mem y !t in
        msg (A.member_message y answer ++ fnl ())
      method print = print_table A.title A.printer !t
    end

    let _ = A.table := (nick,new table_of_A ())::!A.table
    let active c = MySet.mem c !t
    let elements () = MySet.elements !t
  end

let string_table = ref []

let get_string_table k = List.assoc (nickname k) !string_table

module type StringConvertArg =
sig
  val key : option_name
  val title : string
  val member_message : string -> bool -> std_ppcmds
  val synchronous : bool
end

module StringConvert = functor (A : StringConvertArg) ->
struct
  type t = string
  type key = string
  let table = string_table
  let encode x = x
  let subst _ x = x
  let printer = str
  let key = A.key
  let title = A.title
  let member_message = A.member_message
  let synchronous = A.synchronous
end

module MakeStringTable =
  functor (A : StringConvertArg) -> MakeTable (StringConvert(A))

let ref_table = ref []

let get_ref_table k = List.assoc (nickname k) !ref_table

module type RefConvertArg =
sig
  type t
  val encode : reference -> t
  val subst : substitution -> t -> t
  val printer : t -> std_ppcmds
  val key : option_name
  val title : string
  val member_message : t -> bool -> std_ppcmds
  val synchronous : bool
end

module RefConvert = functor (A : RefConvertArg) ->
struct
  type t = A.t
  type key = reference
  let table = ref_table
  let encode = A.encode
  let subst = A.subst
  let printer = A.printer
  let key = A.key
  let title = A.title
  let member_message = A.member_message
  let synchronous = A.synchronous
end

module MakeRefTable =
  functor (A : RefConvertArg) -> MakeTable (RefConvert(A))

(****************************************************************************)
(* 2- Flags.                                                              *)

type 'a option_sig = {
  optsync  : bool;
  optname  : string;
  optkey   : option_name;
  optread  : unit -> 'a;
  optwrite : 'a -> unit }

type option_type = bool * (unit -> value) -> (value -> unit)

module OptionMap =
  Map.Make (struct  type t = option_name let compare = compare end)

let value_tab = ref OptionMap.empty

(* This raises Not_found if option of key [key] is unknown *)

let get_option key = OptionMap.find key !value_tab

let check_key key = try
  let _ = get_option key in
  error "Sorry, this option name is already used"
with Not_found ->
  if List.mem_assoc (nickname key) !string_table
    or List.mem_assoc (nickname key) !ref_table
  then error "Sorry, this option name is already used"

open Summary
open Libobject
open Lib

let declare_option cast uncast
  { optsync=sync; optname=name; optkey=key; optread=read; optwrite=write } =
  check_key key;
  let default = read() in
  (* spiwack: I use two spaces in the nicknames of "local" and "global" objects.
      That way I shouldn't collide with [nickname key] for any [key]. As [key]-s are
       lists of strings *without* spaces. *)
  let (write,lwrite,gwrite) = if sync then
    let (ldecl_obj,_) = (* "Local": doesn't survive section or modules. *)
      declare_object {(default_object ("L  "^nickname key)) with
		       cache_function = (fun (_,v) -> write v);
		       classify_function = (fun _ -> Dispose)}
    in
    let (decl_obj,_) = (* default locality: survives sections but not modules. *)
      declare_object {(default_object (nickname key)) with
		       cache_function = (fun (_,v) -> write v);
		       classify_function = (fun _ -> Dispose);
		       discharge_function = (fun (_,v) -> Some v)}
    in
    let (gdecl_obj,_) = (* "Global": survives section and modules. *)
      declare_object {(default_object ("G  "^nickname key)) with
		       cache_function = (fun (_,v) -> write v);
		       classify_function = (fun v -> Keep v);
		       discharge_function = (fun (_,v) -> Some v);
		       load_function = (fun _ (_,v) -> write v)}
    in
    let _ = declare_summary (nickname key)
	     { freeze_function = read;
	       unfreeze_function = write;
	       init_function = (fun () -> write default) }
    in
    begin fun v -> add_anonymous_leaf (decl_obj v) end ,
    begin fun v -> add_anonymous_leaf (ldecl_obj v) end ,
    begin fun v -> add_anonymous_leaf (gdecl_obj v) end
  else write,write,write
  in
  let cread () = cast (read ()) in
  let cwrite v = write (uncast v) in
  let clwrite v = lwrite (uncast v) in
  let cgwrite v = gwrite (uncast v) in
  value_tab := OptionMap.add key (name,(sync,cread,cwrite,clwrite,cgwrite)) !value_tab;
  write

type 'a write_function = 'a -> unit

let declare_int_option =
  declare_option
    (fun v -> IntValue v)
    (function IntValue v -> v | _ -> anomaly "async_option")
let declare_bool_option =
  declare_option
    (fun v -> BoolValue v)
    (function BoolValue v -> v | _ -> anomaly "async_option")
let declare_string_option =
  declare_option
    (fun v -> StringValue v)
    (function StringValue v -> v | _ -> anomaly "async_option")

(* 3- User accessible commands *)

(* Setting values of options *)

let set_option_value locality check_and_cast key v =
  let (name,(_,read,write,lwrite,gwrite)) =
    try get_option key
    with Not_found -> error ("There is no option "^(nickname key)^".")
  in
  let write = match locality with
    | None -> write
    | Some true -> lwrite
    | Some false -> gwrite
  in
  write (check_and_cast v (read ()))

let bad_type_error () = error "Bad type of value for this option"

let set_int_option_value_gen locality = set_option_value  locality
  (fun v -> function
     | (IntValue _) -> IntValue v
     | _ -> bad_type_error ())
let set_bool_option_value_gen locality = set_option_value locality
  (fun v -> function
     | (BoolValue _) -> BoolValue v
     | _ -> bad_type_error ())
let set_string_option_value_gen locality = set_option_value locality
 (fun v -> function
    | (StringValue _) -> StringValue v
    | _ -> bad_type_error ())

let set_int_option_value = set_int_option_value_gen None
let set_bool_option_value = set_bool_option_value_gen None
let set_string_option_value = set_string_option_value_gen None

(* Printing options/tables *)

let msg_option_value (name,v) =
  match v with
    | BoolValue true  -> str "true"
    | BoolValue false -> str "false"
    | IntValue (Some n) -> int n
    | IntValue None   -> str "undefined"
    | StringValue s   -> str s
    | IdentValue r    -> pr_global_env Idset.empty r

let print_option_value key =
  let (name,(_,read,_,_,_)) = get_option key in
  let s = read () in
  match s with
    | BoolValue b ->
	msg (str ("The "^name^" mode is "^(if b then "on" else "off")) ++
	     fnl ())
    | _ ->
	msg (str ("Current value of "^name^" is ") ++
	     msg_option_value (name,s) ++ fnl ())


let print_tables () =
  msg
    (str "Synchronous options:" ++ fnl () ++
     OptionMap.fold
       (fun key (name,(sync,read,_,_,_)) p ->
	  if sync then
	    p ++ str ("  "^(nickname key)^": ") ++
	    msg_option_value (name,read()) ++ fnl ()
	  else
	    p)
       !value_tab (mt ()) ++
     str "Asynchronous options:" ++ fnl () ++
     OptionMap.fold
       (fun key (name,(sync,read,_,_,_)) p ->
	  if sync then
	    p
	  else
	    p ++ str ("  "^(nickname key)^": ") ++
            msg_option_value (name,read()) ++ fnl ())
       !value_tab (mt ()) ++
     str "Tables:" ++ fnl () ++
     List.fold_right
       (fun (nickkey,_) p -> p ++ str ("  "^nickkey) ++ fnl ())
       !string_table (mt ()) ++
     List.fold_right
       (fun (nickkey,_) p -> p ++ str ("  "^nickkey) ++ fnl ())
       !ref_table (mt ()) ++
     fnl ()
    )


