(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This module manages customization parameters at the vernacular level     *)

open Pp
open Errors
open Util
open Libobject
open Libnames
open Mod_subst

type option_name = string list
type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string

(** Summary of an option status *)
type option_state = {
  opt_sync  : bool;
  opt_depr  : bool;
  opt_name  : string;
  opt_value : option_value;
}

(****************************************************************************)
(* 0- Common things                                                         *)

let nickname table = String.concat " " table

let error_undeclared_key key =
  error ((nickname key)^": no table or option of this type")

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
	  val compare : t -> t -> int
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
      if String.List.mem_assoc nick !A.table then
	error "Sorry, this table name is already used."

    module MySet = Set.Make (struct type t = A.t let compare = A.compare end)

    let t =
      if A.synchronous
      then Summary.ref MySet.empty ~name:nick
      else ref MySet.empty

    let (add_option,remove_option) =
      if A.synchronous then
        let cache_options (_,(f,p)) = match f with
          | GOadd -> t := MySet.add p !t
          | GOrmv -> t := MySet.remove p !t in
        let load_options i o = if Int.equal i 1 then cache_options o in
	let subst_options (subst,(f,p as obj)) = 
	  let p' = A.subst subst p in
	    if p' == p then obj else
	      (f,p')
	in
        let inGo : option_mark * A.t -> obj =
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
      pp (str table_name ++
	   (hov 0
	      (if MySet.is_empty table then str " None" ++ fnl ()
               else MySet.fold
		 (fun a b -> spc () ++ printer a ++ b)
		 table (mt ()) ++ str "." ++ fnl ())))

    class table_of_A () =
    object
      method add x = add_option (A.encode x)
      method remove x = remove_option (A.encode x)
      method mem x =
	let y = A.encode x in
        let answer = MySet.mem y !t in
        msg_info (A.member_message y answer)
      method print = print_table A.title A.printer !t
    end

    let _ = A.table := (nick,new table_of_A ())::!A.table
    let active c = MySet.mem c !t
    let elements () = MySet.elements !t
  end

let string_table = ref []

let get_string_table k = String.List.assoc (nickname k) !string_table

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
  let compare = String.compare
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

let get_ref_table k = String.List.assoc (nickname k) !ref_table

module type RefConvertArg =
sig
  type t
  val compare : t -> t -> int
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
  let compare = A.compare
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
  optdepr  : bool;
  optname  : string;
  optkey   : option_name;
  optread  : unit -> 'a;
  optwrite : 'a -> unit }

module OptionOrd =
struct
  type t = option_name
  let compare opt1 opt2 = List.compare String.compare opt1 opt2
end

module OptionMap = Map.Make(OptionOrd)

let value_tab = ref OptionMap.empty

(* This raises Not_found if option of key [key] is unknown *)

let get_option key = OptionMap.find key !value_tab

let check_key key = try
  let _ = get_option key in
  error "Sorry, this option name is already used."
with Not_found ->
  if String.List.mem_assoc (nickname key) !string_table
    || String.List.mem_assoc (nickname key) !ref_table
  then error "Sorry, this option name is already used."

open Libobject
open Lib

let declare_option cast uncast
  { optsync=sync; optdepr=depr; optname=name; optkey=key; optread=read; optwrite=write } =
  check_key key;
  let default = read() in
  (* spiwack: I use two spaces in the nicknames of "local" and "global" objects.
      That way I shouldn't collide with [nickname key] for any [key]. As [key]-s are
       lists of strings *without* spaces. *)
  let (write,lwrite,gwrite) = if sync then
    let ldecl_obj = (* "Local": doesn't survive section or modules. *)
      declare_object {(default_object ("L  "^nickname key)) with
		       cache_function = (fun (_,v) -> write v);
		       classify_function = (fun _ -> Dispose)}
    in
    let decl_obj = (* default locality: survives sections but not modules. *)
      declare_object {(default_object (nickname key)) with
		       cache_function = (fun (_,v) -> write v);
		       classify_function = (fun _ -> Dispose);
		       discharge_function = (fun (_,v) -> Some v)}
    in
    let gdecl_obj = (* "Global": survives section and modules. *)
      declare_object {(default_object ("G  "^nickname key)) with
		       cache_function = (fun (_,v) -> write v);
		       classify_function = (fun v -> Substitute v);
		       subst_function = (fun (_,v) -> v);
		       discharge_function = (fun (_,v) -> Some v);
		       load_function = (fun _ (_,v) -> write v)}
    in
    let _ = Summary.declare_summary (nickname key)
	     { Summary.freeze_function = (fun _ -> read ());
	       Summary.unfreeze_function = write;
	       Summary.init_function = (fun () -> write default) }
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
  value_tab := OptionMap.add key (name, depr, (sync,cread,cwrite,clwrite,cgwrite)) !value_tab;
  write

type 'a write_function = 'a -> unit

let declare_int_option =
  declare_option
    (fun v -> IntValue v)
    (function IntValue v -> v | _ -> anomaly (Pp.str "async_option"))
let declare_bool_option =
  declare_option
    (fun v -> BoolValue v)
    (function BoolValue v -> v | _ -> anomaly (Pp.str "async_option"))
let declare_string_option =
  declare_option
    (fun v -> StringValue v)
    (function StringValue v -> v | _ -> anomaly (Pp.str "async_option"))

(* 3- User accessible commands *)

(* Setting values of options *)

let set_option_value locality check_and_cast key v =
  let (name, depr, (_,read,write,lwrite,gwrite)) =
    try get_option key
    with Not_found -> error ("There is no option "^(nickname key)^".")
  in
  let write = match locality with
    | None -> write
    | Some true -> lwrite
    | Some false -> gwrite
  in
  write (check_and_cast v (read ()))

let bad_type_error () = error "Bad type of value for this option."

let check_int_value v = function
  | IntValue _ -> IntValue v
  | _ -> bad_type_error ()

let check_bool_value v = function
  | BoolValue _ -> BoolValue v
  | _ -> bad_type_error ()

let check_string_value v = function
  | StringValue _ -> StringValue v
  | _ -> bad_type_error ()

let check_unset_value v = function
  | BoolValue _ -> BoolValue false
  | IntValue _ -> IntValue None
  | _ -> bad_type_error ()

(* Nota: For compatibility reasons, some errors are treated as
   warning. This allows a script to refer to an option that doesn't
   exist anymore *)

let set_int_option_value_gen locality =
  set_option_value locality check_int_value
let set_bool_option_value_gen locality key v =
  try set_option_value locality check_bool_value key v
  with UserError (_,s) -> msg_warning s
let set_string_option_value_gen locality =
  set_option_value locality check_string_value
let unset_option_value_gen locality key =
  try set_option_value locality check_unset_value key ()
  with UserError (_,s) -> msg_warning s

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
(*     | IdentValue r    -> pr_global_env Id.Set.empty r *)

let print_option_value key =
  let (name, depr, (_,read,_,_,_)) = get_option key in
  let s = read () in
  match s with
    | BoolValue b ->
	msg_info (str ("The "^name^" mode is "^(if b then "on" else "off")))
    | _ ->
	msg_info (str ("Current value of "^name^" is ") ++ msg_option_value (name, s))

let get_tables () =
  let tables = !value_tab in
  let fold key (name, depr, (sync,read,_,_,_)) accu =
    let state = {
      opt_sync = sync;
      opt_name = name;
      opt_depr = depr;
      opt_value = read ();
    } in
    OptionMap.add key state accu
  in
  OptionMap.fold fold tables OptionMap.empty

let print_tables () =
  let print_option key name value depr =
    let msg = str ("  "^(nickname key)^": ") ++ msg_option_value (name, value) in
    if depr then msg ++ str " [DEPRECATED]" ++ fnl ()
    else msg ++ fnl ()
  in
  str "Synchronous options:" ++ fnl () ++
    OptionMap.fold
      (fun key (name, depr, (sync,read,_,_,_)) p ->
        if sync then p ++ print_option key name (read ()) depr
        else p)
      !value_tab (mt ()) ++
  str "Asynchronous options:" ++ fnl () ++
    OptionMap.fold
      (fun key (name, depr, (sync,read,_,_,_)) p ->
        if sync then p
        else p ++ print_option key name (read ()) depr)
      !value_tab (mt ()) ++
  str "Tables:" ++ fnl () ++
    List.fold_right
      (fun (nickkey,_) p -> p ++ str ("  "^nickkey) ++ fnl ())
      !string_table (mt ()) ++
    List.fold_right
      (fun (nickkey,_) p -> p ++ str ("  "^nickkey) ++ fnl ())
      !ref_table (mt ()) ++
    fnl ()



