(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* This module manages customization parameters at the vernacular level     *)

open Pp
open Util
open Libobject
open Identifier
open Names

(****************************************************************************)
(* 0- Common things                                                         *)

type option_name =
  | PrimaryTable of string
  | SecondaryTable of string * string

let nickname = function
  | PrimaryTable s         -> s
  | SecondaryTable (s1,s2) -> s1^" "^s2

let error_undeclared_key key =
  error ((nickname key)^": no such table or option")

type value =
  | BoolValue   of bool
  | IntValue    of int
  | StringValue of string
  | IdentValue  of identifier

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
          val check : t -> unit
          val printer : t -> std_ppcmds
          val key : option_name
          val title : string
          val member_message : key -> bool -> string
          val synchronous : bool
        end) ->
  struct
    type option_mark =
      | GOadd
      | GOrmv

    let kn = nickname A.key

    let _ =
      if List.mem_assoc kn !A.table then
	error "Sorry, this table name is already used"

    module MyType = struct type t = A.t let compare = Pervasives.compare end
    module MySet = Set.Make(MyType)

    let t = ref (MySet.empty : MySet.t)

    let _ = 
      if A.synchronous then
	let freeze () = !t in
	let unfreeze c = t := c in
	let init () = t := MySet.empty in
	Summary.declare_summary kn
          { Summary.freeze_function = freeze;
            Summary.unfreeze_function = unfreeze;
            Summary.init_function = init;
	    Summary.survive_section = true }

    let (add_option,remove_option) =
      if A.synchronous then
        let load_options _ = () in
        let cache_options (_,(f,p)) = match f with
          | GOadd -> t := MySet.add p !t
          | GOrmv -> t := MySet.remove p !t in
        let export_options fp = Some fp in
        let (inGo,outGo) =
          Libobject.declare_object {(Libobject.default_object kn) with
                Libobject.load_function = load_options;
		Libobject.open_function = cache_options;
		Libobject.cache_function = cache_options;
		Libobject.export_function = export_options} in
        ((fun c -> Lib.add_anonymous_leaf (inGo (GOadd, c))),
         (fun c -> Lib.add_anonymous_leaf (inGo (GOrmv, c))))
      else
        ((fun c -> t := MySet.add c !t),
         (fun c -> t := MySet.remove c !t))

    let print_table table_name printer table =
      msg (str table_name ++ (hov 0 
           (if MySet.is_empty table then str "None" ++ fnl () 
            else MySet.fold
	      (fun a b -> printer a ++ spc () ++ b ) table (mt ()) )))

    class table_of_A () =
    object
      method add x =
	let c = A.encode x in
        A.check c;
        add_option c
      method remove x = remove_option (A.encode x)
      method mem x = 
        let answer = MySet.mem (A.encode x) !t in
        msg (str (A.member_message x answer)) 
      method print = print_table A.title A.printer !t 
    end

    let _ = A.table := (kn,new table_of_A ())::!A.table
    let active c = MySet.mem c !t
    let elements () = MySet.elements !t
  end

let string_table = ref []

let get_string_table k = List.assoc (nickname k) !string_table

module type StringConvertArg =
sig
  val check : string -> unit
  val key : option_name
  val title : string
  val member_message : string -> bool -> string
  val synchronous : bool
end

module StringConvert = functor (A : StringConvertArg) ->
struct
  type t = string
  type key = string
  let table = string_table
  let encode x = x
  let check = A.check
  let printer s = str s 
  let key = A.key
  let title = A.title
  let member_message = A.member_message
  let synchronous = A.synchronous
end

module MakeStringTable =
  functor (A : StringConvertArg) -> MakeTable (StringConvert(A))

let ident_table = ref []

let get_ident_table k = List.assoc (nickname k) !ident_table

module type IdentConvertArg =
sig
  type t
  val encode : identifier -> t
  val check : t -> unit
  val printer : t -> std_ppcmds
  val key : option_name
  val title : string
  val member_message : identifier -> bool -> string
  val synchronous : bool
end

module IdentConvert = functor (A : IdentConvertArg) -> 
struct
  type t = A.t
  type key = identifier
  let table = ident_table
  let encode = A.encode
  let check = A.check
  let printer = A.printer
  let key = A.key
  let title = A.title
  let member_message = A.member_message
  let synchronous = A.synchronous
end

module MakeIdentTable =
  functor (A : IdentConvertArg) -> MakeTable (IdentConvert(A))

(****************************************************************************)
(* 2- Options                                                               *)

type option_value_ref =
  | OptionBoolRef   of bool   ref
  | OptionIntRef    of int    ref
  | OptionStringRef of string ref

module Key = struct type t = option_name let compare = Pervasives.compare end
module OptionMap = Map.Make(Key)

let sync_value_tab = ref OptionMap.empty
let async_value_tab = ref OptionMap.empty

(* Tools for synchronous options *)

let load_sync_value _ = ()
let cache_sync_value (_,(k,v)) =
  sync_value_tab := OptionMap.add k v !sync_value_tab
let export_sync_value fp = Some fp
let (inOptVal,_) =
  Libobject.declare_object {(default_object "Sync_option_value") with 
 Libobject.load_function = load_sync_value;
      Libobject.open_function = cache_sync_value;
      Libobject.cache_function = cache_sync_value;
      Libobject.export_function = export_sync_value  }

let freeze_sync_table () = !sync_value_tab
let unfreeze_sync_table l = sync_value_tab := l
let init_sync_table () = sync_value_tab := OptionMap.empty
let _ = 
  Summary.declare_summary "Sync_option"
    { Summary.freeze_function = freeze_sync_table;
      Summary.unfreeze_function = unfreeze_sync_table;
      Summary.init_function = init_sync_table;
      Summary.survive_section = true }

(* Tools for handling options *)

type option_type =
  | Sync of  value
  | Async of (unit -> value) * (value -> unit)

(* This raises Not_found if option of key [key] is unknown *)
let get_option key =
  try 
    let (name,(r,w)) = OptionMap.find key !async_value_tab in 
    (name,Async (r,w))
  with Not_found ->
    let (name,i) = OptionMap.find key !sync_value_tab in (name, Sync i)


(* 2-a. Declaring synchronous options *)

type 'a sync_option_sig = {
  optsyncname    : string;
  optsynckey     : option_name;
  optsyncdefault : 'a }

let declare_sync_option (cast,uncast) 
  { optsyncname=name; optsynckey=key; optsyncdefault=default } =
  try 
    let _ = get_option key in
    error "Sorry, this option name is already used"
  with Not_found ->
    if List.mem_assoc (nickname key) !string_table
      or List.mem_assoc (nickname key) !ident_table
    then error "Sorry, this option name is already used";
    sync_value_tab := OptionMap.add key (name,(cast default)) !sync_value_tab;
    fun () -> uncast (snd (OptionMap.find key !sync_value_tab))

type 'a value_function = unit -> 'a

let declare_sync_int_option = declare_sync_option
  ((function vr -> IntValue vr),
   function IntValue x -> x | _ -> anomaly "MakeOption")
let declare_sync_bool_option = declare_sync_option
  ((function vr -> BoolValue vr),
   function BoolValue x -> x | _ -> anomaly "MakeOption")
let declare_sync_string_option = declare_sync_option
  ((function vr -> StringValue vr),
   function StringValue x -> x | _ -> anomaly "MakeOption")

(* 2-b. Declaring synchronous options *)

type 'a async_option_sig = {
  optasyncname  : string;
  optasynckey   : option_name;
  optasyncread  : unit -> 'a;
  optasyncwrite : 'a -> unit }

let declare_async_option cast uncast
  {optasyncname=name;optasynckey=key;optasyncread=read;optasyncwrite=write} =
  try 
    let _ = get_option key in
    error "Sorry, this option name is already used"
  with Not_found ->
    if List.mem_assoc (nickname key) !string_table
      or List.mem_assoc (nickname key) !ident_table then 
      error "Sorry, this option name is already used";
    let cread () = cast (read ()) in
    let cwrite v = write (uncast v) in
    async_value_tab := OptionMap.add key (name,(cread,cwrite)) !async_value_tab

let declare_async_int_option =
  declare_async_option 
    (fun v -> IntValue v)
    (function IntValue v -> v | _ -> anomaly "async_option")
let declare_async_bool_option =
  declare_async_option
    (fun v -> BoolValue v)
    (function BoolValue v -> v | _ -> anomaly "async_option")
let declare_async_string_option =
  declare_async_option
    (fun v -> StringValue v)
    (function StringValue v -> v | _ -> anomaly "async_option")


(* 3- User accessible commands *)

(* Setting values of options *)

let set_option_value check_and_cast key v =
  let (name,info) =
    try get_option key
    with Not_found -> error ("There is no option "^(nickname key)^".")
  in
  match info with
    | Sync  current  ->
      	Lib.add_anonymous_leaf
	  (inOptVal (key,(name,check_and_cast v current)))
    | Async (read,write) -> write (check_and_cast v (read ()))

let bad_type_error () = error "Bad type of value for this option"

let set_int_option_value = set_option_value
  (fun v -> function 
     | (IntValue _) -> IntValue v
     | _ -> bad_type_error ())
let set_bool_option_value = set_option_value
  (fun v -> function 
     | (BoolValue _) -> BoolValue v
     | _ -> bad_type_error ())
let set_string_option_value = set_option_value
 (fun v -> function 
    | (StringValue _) -> StringValue v
    | _ -> bad_type_error ())

(* Printing options/tables *)

let msg_sync_option_value (name,v) =
  match v with
    | BoolValue true  -> str "true" 
    | BoolValue false -> str "false" 
    | IntValue n      -> int n 
    | StringValue s   -> str s 
    | IdentValue id    -> pr_id id 

let msg_async_option_value (name,vref) =
  match vref with
    | OptionBoolRef {contents=true}  -> str "true" 
    | OptionBoolRef {contents=false} -> str "false" 
    | OptionIntRef  r     -> int !r 
    | OptionStringRef r   -> str !r 

let print_option_value key =
  let (name,info) = get_option key in
  let s = match info with
    | Sync v -> msg_sync_option_value (name,v)
      | Async (read,write) -> msg_sync_option_value (name,read ())
  in msg (str ("Current value of "^name^" is ") ++ s ++ fnl ()) 

let print_tables () =
  msg
  (str "Synchronous options:" ++ fnl () ++
     OptionMap.fold 
       (fun key (name,v) p -> p ++ str ("  "^(nickname key)^": ") ++
				 msg_sync_option_value (name,v) ++ fnl () )
       !sync_value_tab (mt ()) ++
     str "Asynchronous options:" ++ fnl () ++
     OptionMap.fold 
       (fun key (name,(read,write)) p -> p ++ str ("  "^(nickname key)^": ") ++
                                  msg_sync_option_value (name,read()) ++ fnl () )
	    !async_value_tab (mt ()) ++
     str "Tables:" ++ fnl () ++
     List.fold_right
       (fun (nickkey,_) p -> p ++ str ("  "^nickkey) ++ fnl () )
       !string_table (mt ()) ++
     List.fold_right
       (fun (nickkey,_) p -> p ++ str ("  "^nickkey) ++ fnl () )
       !ident_table (mt ()) ++
     fnl ())
 

