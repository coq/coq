(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module manages customization parameters at the vernacular level     *)

open Pp
open CErrors
open Util
open Libobject
open Libnames
open Mod_subst

type option_name = string list
type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | StringOptValue of string option

(** Summary of an option status *)
type option_state = {
  opt_depr  : bool;
  opt_name  : string;
  opt_value : option_value;
}

(****************************************************************************)
(* 0- Common things                                                         *)

let nickname table = String.concat " " table

let error_undeclared_key key =
  user_err ~hdr:"Goptions" (str (nickname key) ++ str ": no table or option of this type")

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
          val printer : t -> Pp.t
          val key : option_name
          val title : string
          val member_message : t -> bool -> Pp.t
        end) ->
  struct
    type option_mark =
      | GOadd
      | GOrmv

    let nick = nickname A.key

    let _ =
      if String.List.mem_assoc nick !A.table then
	user_err Pp.(str "Sorry, this table name is already used.")

    module MySet = Set.Make (struct type t = A.t let compare = A.compare end)

    let t = Summary.ref MySet.empty ~name:nick

    let (add_option,remove_option) =
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

    let print_table table_name printer table =
      Feedback.msg_notice
        (str table_name ++
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
        Feedback.msg_info (A.member_message y answer)
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
  val member_message : string -> bool -> Pp.t
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
end

module MakeStringTable =
  functor (A : StringConvertArg) -> MakeTable (StringConvert(A))

let ref_table = ref []

let get_ref_table k = String.List.assoc (nickname k) !ref_table

module type RefConvertArg =
sig
  type t
  val compare : t -> t -> int
  val encode : qualid -> t
  val subst : substitution -> t -> t
  val printer : t -> Pp.t
  val key : option_name
  val title : string
  val member_message : t -> bool -> Pp.t
end

module RefConvert = functor (A : RefConvertArg) ->
struct
  type t = A.t
  type key = qualid
  let compare = A.compare
  let table = ref_table
  let encode = A.encode
  let subst = A.subst
  let printer = A.printer
  let key = A.key
  let title = A.title
  let member_message = A.member_message
end

module MakeRefTable =
  functor (A : RefConvertArg) -> MakeTable (RefConvert(A))

(****************************************************************************)
(* 2- Flags.                                                              *)

type 'a option_sig = {
  optdepr  : bool;
  optname  : string;
  optkey   : option_name;
  optread  : unit -> 'a;
  optwrite : 'a -> unit }

type option_locality = OptDefault | OptLocal | OptExport | OptGlobal

type option_mod = OptSet | OptAppend

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
  user_err Pp.(str "Sorry, this option name is already used.")
with Not_found ->
  if String.List.mem_assoc (nickname key) !string_table
    || String.List.mem_assoc (nickname key) !ref_table
  then user_err Pp.(str "Sorry, this option name is already used.")

open Libobject

let warn_deprecated_option =
  CWarnings.create ~name:"deprecated-option" ~category:"deprecated"
         (fun key -> str "Option" ++ spc () ++ str (nickname key) ++
                       strbrk " is deprecated")

let declare_option cast uncast append ?(preprocess = fun x -> x)
  { optdepr=depr; optname=name; optkey=key; optread=read; optwrite=write } =
  check_key key;
  let default = read() in
  let change =
      let _ = Summary.declare_summary (nickname key)
        { Summary.freeze_function = (fun _ -> read ());
          Summary.unfreeze_function = write;
          Summary.init_function = (fun () -> write default) } in
      let cache_options (_,(l,m,v)) =
        match m with
        | OptSet -> write v
        | OptAppend -> write (append (read ()) v) in
      let load_options i (_, (l, _, _) as o) = match l with
      | OptGlobal -> cache_options o
      | OptExport -> ()
      | OptLocal | OptDefault ->
        (** Ruled out by classify_function *)
        assert false
      in
      let open_options i  (_, (l, _, _) as o) = match l with
      | OptExport -> if Int.equal i 1 then cache_options o
      | OptGlobal -> ()
      | OptLocal | OptDefault ->
        (** Ruled out by classify_function *)
        assert false
      in
      let subst_options (subst,obj) = obj in
      let discharge_options (_,(l,_,_ as o)) =
        match l with OptLocal -> None | (OptExport | OptGlobal | OptDefault) -> Some o in
      let classify_options (l,_,_ as o) =
        match l with (OptExport | OptGlobal) -> Substitute o | (OptLocal | OptDefault) -> Dispose in
      let options : option_locality * option_mod * _ -> obj =
        declare_object
          { (default_object (nickname key)) with
            load_function = load_options;
            open_function = open_options;
            cache_function = cache_options;
            subst_function = subst_options;
            discharge_function = discharge_options;
            classify_function = classify_options } in
      (fun l m v -> let v = preprocess v in Lib.add_anonymous_leaf (options (l, m, v)))
  in
  let warn () = if depr then warn_deprecated_option key in
  let cread () = cast (read ()) in
  let cwrite l v = warn (); change l OptSet (uncast v) in
  let cappend l v = warn (); change l OptAppend (uncast v) in
  value_tab := OptionMap.add key (name, depr, (cread,cwrite,cappend)) !value_tab;
  write

type 'a write_function = 'a -> unit

let declare_int_option =
  declare_option
    (fun v -> IntValue v)
    (function IntValue v -> v | _ -> anomaly (Pp.str "async_option."))
    (fun _ _ -> anomaly (Pp.str "async_option."))
let declare_bool_option =
  declare_option
    (fun v -> BoolValue v)
    (function BoolValue v -> v | _ -> anomaly (Pp.str "async_option."))
    (fun _ _ -> anomaly (Pp.str "async_option."))
let declare_string_option =
  declare_option
    (fun v -> StringValue v)
    (function StringValue v -> v | _ -> anomaly (Pp.str "async_option."))
    (fun x y -> x^","^y)
let declare_stringopt_option =
  declare_option
    (fun v -> StringOptValue v)
    (function StringOptValue v -> v | _ -> anomaly (Pp.str "async_option."))
    (fun _ _ -> anomaly (Pp.str "async_option."))

(* 3- User accessible commands *)

(* Setting values of options *)

let warn_unknown_option =
  CWarnings.create ~name:"unknown-option" ~category:"option"
                   (fun key -> strbrk "There is no option " ++
                                 str (nickname key) ++ str ".")

let set_option_value ?(locality = OptDefault) check_and_cast key v =
  let opt = try Some (get_option key) with Not_found -> None in
  match opt with
  | None -> warn_unknown_option key
  | Some (name, depr, (read,write,append)) ->
    write locality (check_and_cast v (read ()))

let show_value_type = function
  | BoolValue _ -> "bool"
  | IntValue _ -> "int"
  | StringValue _ -> "string"
  | StringOptValue _ -> "string"

let bad_type_error opt_value actual_type =
  user_err Pp.(str "Bad type of value for this option:" ++ spc() ++
               str "expected " ++ str (show_value_type opt_value) ++
               str ", got " ++ str actual_type ++ str ".")

let check_int_value v = function
  | IntValue _ -> IntValue v
  | optv -> bad_type_error optv "int"

let check_bool_value v = function
  | BoolValue _ -> BoolValue v
  | optv -> bad_type_error optv "bool"

let check_string_value v = function
  | StringValue _ -> StringValue v
  | StringOptValue _ -> StringOptValue (Some v)
  | optv -> bad_type_error optv "string"

let check_unset_value v = function
  | BoolValue _ -> BoolValue false
  | IntValue _ -> IntValue None
  | StringOptValue _ -> StringOptValue None
  | optv -> bad_type_error optv "nothing"

(* Nota: For compatibility reasons, some errors are treated as
   warning. This allows a script to refer to an option that doesn't
   exist anymore *)

let set_int_option_value_gen ?locality =
  set_option_value ?locality check_int_value
let set_bool_option_value_gen ?locality key v =
  set_option_value ?locality check_bool_value key v
let set_string_option_value_gen ?locality =
  set_option_value ?locality check_string_value
let unset_option_value_gen ?locality key =
  set_option_value ?locality check_unset_value key ()

let set_string_option_append_value_gen ?(locality = OptDefault) key v =
  let opt = try Some (get_option key) with Not_found -> None in
  match opt with
  | None -> warn_unknown_option key
  | Some (name, depr, (read,write,append)) ->
    append locality (check_string_value v (read ()))

let set_int_option_value opt v = set_int_option_value_gen opt v
let set_bool_option_value opt v = set_bool_option_value_gen opt v
let set_string_option_value opt v = set_string_option_value_gen opt v

(* Printing options/tables *)

let msg_option_value (name,v) =
  match v with
    | BoolValue true  -> str "on"
    | BoolValue false -> str "off"
    | IntValue (Some n) -> int n
    | IntValue None   -> str "undefined"
    | StringValue s   -> quote (str s)
    | StringOptValue None   -> str"undefined"
    | StringOptValue (Some s)   -> quote (str s)
(*     | IdentValue r    -> pr_global_env Id.Set.empty r *)

let print_option_value key =
  let (name, depr, (read,_,_)) = get_option key in
  let s = read () in
  match s with
    | BoolValue b ->
	Feedback.msg_info (str "The " ++ str name ++ str " mode is " ++ str (if b then "on" else "off"))
    | _ ->
	Feedback.msg_info (str "Current value of " ++ str name ++ str " is " ++ msg_option_value (name, s))

let get_tables () =
  let tables = !value_tab in
  let fold key (name, depr, (read,_,_)) accu =
    let state = {
      opt_name = name;
      opt_depr = depr;
      opt_value = read ();
    } in
    OptionMap.add key state accu
  in
  OptionMap.fold fold tables OptionMap.empty

let print_tables () =
  let print_option key name value depr =
    let msg = str "  " ++ str (nickname key) ++ str ": " ++ msg_option_value (name, value) in
    if depr then msg ++ str " [DEPRECATED]" ++ fnl ()
    else msg ++ fnl ()
  in
  str "Options:" ++ fnl () ++
    OptionMap.fold
      (fun key (name, depr, (read,_,_)) p ->
        p ++ print_option key name (read ()) depr)
      !value_tab (mt ()) ++
  str "Tables:" ++ fnl () ++
    List.fold_right
      (fun (nickkey,_) p -> p ++ str "  " ++ str nickkey ++ fnl ())
      !string_table (mt ()) ++
    List.fold_right
      (fun (nickkey,_) p -> p ++ str "  " ++ str nickkey ++ fnl ())
      !ref_table (mt ()) ++
    fnl ()



