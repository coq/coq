
(* $Id$ *)

(* This module manages customization parameters at the vernacular level     *)

open Pp
open Util
open Libobject
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

(****************************************************************************)
(* 1- Tables                                                                *)

let param_table = ref []

let get_option_table k = List.assoc (nickname k) !param_table

module MakeTable =
  functor
   (A : sig
	  type t
          val encode : identifier -> t
          val check : t -> unit
          val decode : t -> section_path
          val key : option_name
          val title : string
          val member_message : identifier -> bool -> string
          val synchronous : bool
        end) ->
  struct
    type option_mark =
      | GOadd
      | GOrmv

    let kn = nickname A.key

    let _ =
      if List.mem_assoc kn !param_table then
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
            Summary.init_function = init }

    let (add_option,remove_option) =
      if A.synchronous then
        let load_options _ = () in
	let open_options _ = () in
        let cache_options (_,(f,p)) = match f with
          | GOadd -> t := MySet.add p !t
          | GOrmv -> t := MySet.remove p !t in
        let specification_options fp = fp in
        let (inGo,outGo) =
          Libobject.declare_object (kn,
              { Libobject.load_function = load_options;
		Libobject.open_function = open_options;
		Libobject.cache_function = cache_options;
		Libobject.specification_function = specification_options}) in
        ((fun c -> Lib.add_anonymous_leaf (inGo (GOadd, c))),
         (fun c -> Lib.add_anonymous_leaf (inGo (GOrmv, c))))
      else
        ((fun c -> t := MySet.add c !t),
         (fun c -> t := MySet.remove c !t))

    let print_table table_name printer table =
      mSG ([< 'sTR table_name ; (hOV 0 
           (if MySet.is_empty table then [< 'sTR "None" ; 'fNL >]
            else MySet.fold (fun a b -> [< printer a; b >]) table [<>])) >])

    class table_of_A () =
    object
      method add id =
        let c = A.encode id in
        A.check c;
        add_option c
      method remove id = remove_option (A.encode id)
      method mem id = 
        let answer = MySet.mem (A.encode id) !t in
        mSG [< 'sTR (A.member_message id answer) >]
      method print =
        let pr x = [< 'sTR(string_of_path (A.decode x)); 'fNL >] in
        print_table A.title pr !t 
    end

    let _ = param_table := (kn,new table_of_A ())::!param_table
    let active c = MySet.mem c !t

  end

(****************************************************************************)
(* 2- Options                                                               *)

type option_value_ref =
  | OptionBoolRef   of bool   ref
  | OptionIntRef    of int    ref
  | OptionStringRef of string ref

type option_value =
  | OptionBool   of bool
  | OptionInt    of int
  | OptionString of string

module Key = struct type t = option_name let compare = Pervasives.compare end
module OptionMap = Map.Make(Key)

let sync_value_tab = ref OptionMap.empty
let async_value_tab = ref OptionMap.empty

(* Tools for synchronous options *)

let load_sync_value _ = ()
let open_sync_value _ = ()
let cache_sync_value (_,(k,v)) =
  sync_value_tab := OptionMap.add k v !sync_value_tab
let spec_sync_value fp = fp
let (inOptVal,_) =
   Libobject.declare_object ("Sync_option_value",
     {Libobject.load_function = load_sync_value;
      Libobject.open_function = open_sync_value;
      Libobject.cache_function = cache_sync_value;
      Libobject.specification_function = spec_sync_value})

let freeze_sync_table () = !sync_value_tab
let unfreeze_sync_table l = sync_value_tab := l
let init_sync_table () = sync_value_tab := OptionMap.empty
let _ = 
  Summary.declare_summary "Sync_option"
    { Summary.freeze_function = freeze_sync_table;
      Summary.unfreeze_function = unfreeze_sync_table;
      Summary.init_function = init_sync_table }

(* Tools for handling options *)

type option_type =
  | Sync of  option_value
  | Async of (unit -> option_value) * (option_value -> unit)

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
    if List.mem_assoc (nickname key) !param_table
    then error "Sorry, this option name is already used";
    sync_value_tab := OptionMap.add key (name,(cast default)) !sync_value_tab;
    fun () -> uncast (snd (OptionMap.find key !sync_value_tab))

type 'a value_function = unit -> 'a

let declare_sync_int_option = declare_sync_option
  ((function vr -> OptionInt vr),
   function OptionInt x -> x | _ -> anomaly "MakeOption")
let declare_sync_bool_option = declare_sync_option
  ((function vr -> OptionBool vr),
   function OptionBool x -> x | _ -> anomaly "MakeOption")
let declare_sync_string_option = declare_sync_option
  ((function vr -> OptionString vr),
   function OptionString x -> x | _ -> anomaly "MakeOption")

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
    if List.mem_assoc (nickname key) !param_table
    then error "Sorry, this option name is already used";
    let cread () = cast (read ()) in
    let cwrite v = write (uncast v) in
    async_value_tab := OptionMap.add key (name,(cread,cwrite)) !async_value_tab

let declare_async_int_option =
  declare_async_option 
    (fun v -> OptionInt v)
    (function OptionInt v -> v | _ -> anomaly "async_option")
let declare_async_bool_option =
  declare_async_option
    (fun v -> OptionBool v)
    (function OptionBool v -> v | _ -> anomaly "async_option")
let declare_async_string_option =
  declare_async_option
    (fun v -> OptionString v)
    (function OptionString v -> v | _ -> anomaly "async_option")


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
     | (OptionInt _) -> OptionInt v
     | _ -> bad_type_error ())
let set_bool_option_value = set_option_value
  (fun v -> function 
     | (OptionBool _) -> OptionBool v
     | _ -> bad_type_error ())
let set_string_option_value = set_option_value
 (fun v -> function 
    | (OptionString _) -> OptionString v
    | _ -> bad_type_error ())

(* Printing options/tables *)

let msg_sync_option_value (name,v) =
  match v with
    | OptionBool true  -> [< 'sTR "true" >]
    | OptionBool false -> [< 'sTR "false" >]
    | OptionInt n      -> [< 'iNT n >]
    | OptionString s   -> [< 'sTR s >]

let msg_async_option_value (name,vref) =
  match vref with
    | OptionBoolRef {contents=true}  -> [< 'sTR "true" >]
    | OptionBoolRef {contents=false} -> [< 'sTR "false" >]
    | OptionIntRef  r     -> [< 'iNT !r >]
    | OptionStringRef r   -> [< 'sTR !r >]

let print_option_value key =
  let (name,info) = get_option key in
  let s = match info with
    | Sync v -> msg_sync_option_value (name,v)
      | Async (read,write) -> msg_sync_option_value (name,read ())
  in mSG [< 'sTR ("Current value of "^name^" is "); s; 'fNL >]

let print_tables () =
  mSG
  [< 'sTR "Synchronous options:"; 'fNL; 
     OptionMap.fold 
       (fun key (name,v) p -> [< p; 'sTR ("  "^(nickname key)^": ");
				 msg_sync_option_value (name,v); 'fNL >])
       !sync_value_tab [<>];
     'sTR "Asynchronous options:"; 'fNL;
     OptionMap.fold 
       (fun key (name,(read,write)) p -> [< p; 'sTR ("  "^(nickname key)^": ");
                                  msg_sync_option_value (name,read()); 'fNL >])
	    !async_value_tab [<>];
     'sTR "Tables:"; 'fNL;
     List.fold_right
       (fun (nickkey,_) p -> [< p; 'sTR ("  "^nickkey); 'fNL >])
       !param_table [<>];
     'fNL
 >]

