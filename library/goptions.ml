(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module manages customization parameters at the vernacular level     *)

open Util
open Summary.Stage

type option_name = string list
type option_value =
  | BoolValue   of bool
  | IntValue    of int option
  | StringValue of string
  | StringOptValue of string option

type table_value =
  | StringRefValue of string
  | QualidRefValue of Libnames.qualid

(** Summary of an option status *)
type option_state = {
  opt_depr  : Deprecation.t option;
  opt_value : option_value;
}

(****************************************************************************)
(* 0- Common things                                                         *)

let nickname table = String.concat " " table

let error_no_table_of_this_type ~kind key =
  CErrors.user_err
    Pp.(str ("There is no " ^ kind ^ "-valued table with this name: \""
      ^ nickname key ^ "\"."))

let error_undeclared_key key =
  CErrors.user_err
    Pp.(str ("There is no flag, option or table with this name: \""
      ^ nickname key ^ "\"."))

(****************************************************************************)
(* 1- Tables                                                                *)

type 'a table_of_A =  {
  add : Environ.env -> 'a -> unit;
  remove : Environ.env -> 'a -> unit;
  mem : Environ.env -> 'a -> unit;
  print : unit -> unit;
}

let opts_cat = Libobject.create_category "options"

module MakeTable =
  functor
   (A : sig
          type t
          type key
          module Set : CSig.SetS with type elt = t
          val table : (string * key table_of_A) list ref
          val encode : Environ.env -> key -> t
          val subst : Mod_subst.substitution -> t -> t
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

    let () =
      if String.List.mem_assoc nick !A.table then
        CErrors.user_err
          Pp.(strbrk "Sorry, this table name (" ++ str nick
            ++ strbrk ") is already used.")

    module MySet = A.Set

    let t = Summary.ref ~stage:Summary.Stage.Synterp MySet.empty ~name:nick

    let (add_option,remove_option) =
        let cache_options (f,p) = match f with
          | GOadd -> t := MySet.add p !t
          | GOrmv -> t := MySet.remove p !t in
        let load_options i o = if Int.equal i 1 then cache_options o in
        let subst_options (subst,(f,p as obj)) =
          let p' = A.subst subst p in
            if p' == p then obj else
              (f,p')
        in
        let inGo : option_mark * A.t -> Libobject.obj =
          Libobject.declare_object {(Libobject.default_object nick) with
                Libobject.object_stage = Summary.Stage.Synterp;
                Libobject.load_function = load_options;
                Libobject.open_function = Libobject.simple_open ~cat:opts_cat load_options;
                Libobject.cache_function = cache_options;
                Libobject.subst_function = subst_options;
                Libobject.classify_function = (fun x -> Substitute)}
        in
        ((fun c -> Lib.add_leaf (inGo (GOadd, c))),
         (fun c -> Lib.add_leaf (inGo (GOrmv, c))))

    let print_table table_name printer table =
      let open Pp in
      let pp = if MySet.is_empty table then str table_name ++ str " is empty."
        else
          str table_name ++ str ":" ++ spc() ++
          (hov 0 (prlist_with_sep spc printer (MySet.elements table))) ++
          str "."
      in
      Feedback.msg_notice pp

    let table_of_A = {
       add = (fun env x -> add_option (A.encode env x));
       remove = (fun env x -> remove_option (A.encode env x));
       mem = (fun env x ->
        let y = A.encode env x in
        let answer = MySet.mem y !t in
        Feedback.msg_info (A.member_message y answer));
       print = (fun () -> print_table A.title A.printer !t);
     }

    let _ = A.table := (nick, table_of_A)::!A.table

    let v () = !t
    let active x = A.Set.mem x !t
    let set x b = if b then add_option x else remove_option x
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
  module Set = CString.Set
  let table = string_table
  let encode _env x = x
  let subst _ x = x
  let printer = Pp.str
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
  module Set : CSig.SetS with type elt = t
  val encode : Environ.env -> Libnames.qualid -> t
  val subst : Mod_subst.substitution -> t -> t
  val printer : t -> Pp.t
  val key : option_name
  val title : string
  val member_message : t -> bool -> Pp.t
end

module RefConvert = functor (A : RefConvertArg) ->
struct
  type t = A.t
  type key = Libnames.qualid
  module Set = A.Set
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

type iter_table_aux = { aux : 'a. 'a table_of_A -> Environ.env -> 'a -> unit }

let iter_table env f key lv =
  let aux = function
    | StringRefValue s ->
       begin
         try f.aux (get_string_table key) env s
         with Not_found -> error_no_table_of_this_type ~kind:"string" key
       end
    | QualidRefValue locqid ->
       begin
         try f.aux (get_ref_table key) env locqid
         with Not_found -> error_no_table_of_this_type ~kind:"qualid" key
       end
  in
  List.iter aux lv

(****************************************************************************)
(* 2- Flags.                                                              *)

type 'a option_sig = {
  optstage : Summary.Stage.t;
  optdepr  : Deprecation.t option;
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
  CErrors.user_err Pp.(str "Sorry, this option name ("
    ++ str (nickname key) ++ str ") is already used.")
with Not_found ->
  if String.List.mem_assoc (nickname key) !string_table
    || String.List.mem_assoc (nickname key) !ref_table
  then CErrors.user_err Pp.(str "Sorry, this option name ("
    ++ str (nickname key) ++ str ") is already used.")

open Libobject

let warn_deprecated_option =
  Deprecation.create_warning ~object_name:"Option" ~warning_name_if_no_since:"deprecated-option"
    (fun key -> Pp.str (nickname key))

let declare_option cast uncast append ?(preprocess = fun x -> x)
  { optstage=stage; optdepr=depr; optkey=key; optread=read; optwrite=write } =
  check_key key;
  let default = read() in
  let change =
      let () = Summary.declare_summary (nickname key)
        { stage;
          Summary.freeze_function = read;
          Summary.unfreeze_function = write;
          Summary.init_function = (fun () -> write default) } in
      let cache_options (l,m,v) =
        match m with
        | OptSet -> write v
        | OptAppend -> write (append (read ()) v) in
      let load_options i (l, _, _ as o) = match l with
      | OptGlobal -> cache_options o
      | OptExport -> ()
      | OptLocal | OptDefault ->
        (* Ruled out by classify_function *)
        assert false
      in
      let open_options i  (l, _, _ as o) = match l with
      | OptExport -> if Int.equal i 1 then cache_options o
      | OptGlobal -> ()
      | OptLocal | OptDefault ->
        (* Ruled out by classify_function *)
        assert false
      in
      let subst_options (subst,obj) = obj in
      let discharge_options (l,_,_ as o) =
        match l with OptLocal -> None | (OptExport | OptGlobal | OptDefault) -> Some o in
      let classify_options (l,_,_) =
        match l with (OptExport | OptGlobal) -> Substitute | (OptLocal | OptDefault) -> Dispose in
      let options : option_locality * option_mod * _ -> obj =
        declare_object
          { (default_object (nickname key)) with
            object_stage = stage;
            load_function = load_options;
            open_function = simple_open ~cat:opts_cat open_options;
            cache_function = cache_options;
            subst_function = subst_options;
            discharge_function = discharge_options;
            classify_function = classify_options } in
      (fun l m v -> let v = preprocess v in Lib.add_leaf (options (l, m, v)))
  in
  let warn () = depr |> Option.iter (fun depr -> warn_deprecated_option (key,depr)) in
  let cread () = cast (read ()) in
  let cwrite l v = warn (); change l OptSet (uncast v) in
  let cappend l v = warn (); change l OptAppend (uncast v) in
  value_tab := OptionMap.add key (depr, stage, (cread,cwrite,cappend)) !value_tab

let declare_int_option =
  declare_option
    (fun v -> IntValue v)
    (function IntValue v -> v | _ -> CErrors.anomaly (Pp.str "async_option."))
    (fun _ _ -> CErrors.anomaly (Pp.str "async_option."))
let declare_bool_option =
  declare_option
    (fun v -> BoolValue v)
    (function BoolValue v -> v | _ -> CErrors.anomaly (Pp.str "async_option."))
    (fun _ _ -> CErrors.anomaly (Pp.str "async_option."))
let declare_string_option =
  declare_option
    (fun v -> StringValue v)
    (function StringValue v -> v | _ -> CErrors.anomaly (Pp.str "async_option."))
    (fun x y -> x^","^y)

let declare_stringopt_option =
  declare_option
    (fun v -> StringOptValue v)
    (function StringOptValue v -> v | _ -> CErrors.anomaly (Pp.str "async_option."))
    (fun _ _ -> CErrors.anomaly (Pp.str "async_option."))

type 'a getter = { get : unit -> 'a }

type 'a opt_decl = ?stage:Summary.Stage.t -> ?depr:Deprecation.t -> key:option_name -> value:'a -> unit -> 'a getter

let declare_int_option_and_ref ?(stage=Interp) ?depr ~key ~(value:int) () =
  let r_opt = ref value in
  let optwrite v = r_opt := Option.default value v in
  let optread () = Some !r_opt in
  let () = declare_int_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread;
      optwrite;
    } in
  { get = fun () -> !r_opt }

let declare_intopt_option_and_ref ?(stage=Interp) ?depr ~key ~value () =
  let r_opt = ref value in
  let optwrite v = r_opt := v in
  let optread () = !r_opt in
  let () = declare_int_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread; optwrite
    } in
  { get = optread }

let declare_nat_option_and_ref ?(stage=Interp) ?depr ~key ~(value:int) () =
  assert (value >= 0);
  let r_opt = ref value in
  let optwrite v =
    let v = Option.default value v in
    if v < 0 then
      CErrors.user_err Pp.(str "This option expects a non-negative value.");
    r_opt := v
  in
  let optread () = Some !r_opt in
  let () = declare_int_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread; optwrite
    } in
  { get = fun () -> !r_opt }

let declare_bool_option_and_ref ?(stage=Interp) ?depr ~key ~(value:bool) () =
  let r_opt = ref value in
  let optwrite v = r_opt := v in
  let optread () = !r_opt in
  let () = declare_bool_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread; optwrite
    } in
  { get = optread }

let declare_string_option_and_ref ?(stage=Interp) ?depr ~key ~(value:string) () =
  let r_opt = ref value in
  let optwrite v = r_opt := Option.default value v in
  let optread () = Some !r_opt in
  let () = declare_stringopt_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread; optwrite
    } in
  { get = fun () -> !r_opt }

let declare_stringopt_option_and_ref ?(stage=Interp) ?depr ~key ~value () =
  let r_opt = ref value in
  let optwrite v = r_opt := v in
  let optread () = !r_opt in
  let () = declare_stringopt_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread; optwrite
    } in
  { get = optread }

let declare_interpreted_string_option_and_ref from_string to_string ?(stage=Interp) ?depr ~key ~(value:'a) () =
  let r_opt = ref value in
  let optwrite v = r_opt := Option.default value @@ Option.map from_string v in
  let optread () = Some (to_string !r_opt) in
  let () = declare_stringopt_option {
      optstage = stage;
      optdepr = depr;
      optkey = key;
      optread; optwrite
    } in
  { get = fun () -> !r_opt }

(* 3- User accessible commands *)

(* Setting values of options *)

let warn_unknown_option =
  CWarnings.create
    ~name:"unknown-option"
    Pp.(fun key -> strbrk "There is no flag or option with this name: \"" ++
                  str (nickname key) ++ str "\".")

let get_option_value key =
  try
    let (_,_,(read,write,append)) = get_option key in
    Some read
  with Not_found -> None

(** Sets the option only if [stage] matches the option declaration or if [stage]
  is omitted. If the option is not found, a warning is emitted only if the stage
  is [Interp] or omitted. *)
let set_option_value ?(locality = OptDefault) ?stage check_and_cast key v =
  let opt = try Some (get_option key) with Not_found -> None in
  match opt with
  | None -> begin match stage with None | Some Summary.Stage.Interp -> warn_unknown_option key | _ -> () end
  | Some (depr, option_stage, (read,write,append)) ->
    if Option.cata (fun s -> s = option_stage) true stage then
      write locality (check_and_cast v (read ()))

let bad_type_error ~expected ~got =
  CErrors.user_err Pp.(strbrk "Bad type of value for this option:" ++ spc()
    ++ str "expected " ++ str expected ++ str ", got " ++ str got ++ str ".")

let error_flag () =
  CErrors.user_err Pp.(str "This is a flag. It does not take a value.")

let check_int_value v = function
  | BoolValue _ -> error_flag ()
  | IntValue _ -> IntValue v
  | StringValue _ | StringOptValue _ ->
     bad_type_error ~expected:"string" ~got:"int"

let check_bool_value v = function
  | BoolValue _ -> BoolValue v
  | _ ->
      CErrors.user_err
        Pp.(str "This is an option. A value must be provided.")

let check_string_value v = function
  | BoolValue _ -> error_flag ()
  | IntValue _ -> bad_type_error ~expected:"int" ~got:"string"
  | StringValue _ -> StringValue v
  | StringOptValue _ -> StringOptValue (Some v)

let check_unset_value v = function
  | BoolValue _ -> BoolValue false
  | IntValue _ -> IntValue None
  | StringOptValue _ -> StringOptValue None
  | StringValue _ ->
      CErrors.user_err
        Pp.(str "This option does not support the \"Unset\" command.")

(* Nota: For compatibility reasons, some errors are treated as
   warnings. This allows a script to refer to an option that doesn't
   exist anymore *)

let set_int_option_value_gen ?locality ?stage =
  set_option_value ?locality ?stage check_int_value
let set_bool_option_value_gen ?locality ?stage key v =
  set_option_value ?locality ?stage check_bool_value key v
let set_string_option_value_gen ?locality ?stage =
  set_option_value ?locality ?stage check_string_value
let unset_option_value_gen ?locality ?stage key =
  set_option_value ?locality ?stage check_unset_value key ()

let set_string_option_append_value_gen ?(locality = OptDefault) ?stage key v =
  let opt = try Some (get_option key) with Not_found -> None in
  match opt with
  | None -> warn_unknown_option key
  | Some (depr, option_stage, (read,write,append)) ->
    if Option.cata (fun s -> s = option_stage) true stage then
      append locality (check_string_value v (read ()))

let set_int_option_value ?stage opt v = set_int_option_value_gen ?stage opt v
let set_bool_option_value ?stage opt v = set_bool_option_value_gen ?stage opt v
let set_string_option_value ?stage opt v = set_string_option_value_gen ?stage opt v

(* Printing options/tables *)

let msg_option_value = Pp.(function
  | BoolValue true -> str "on"
  | BoolValue false -> str "off"
  | IntValue (Some n) -> int n
  | IntValue None -> str "undefined"
  | StringValue s -> quote (str s)
  | StringOptValue None -> str "undefined"
  | StringOptValue (Some s) -> quote (str s))

let print_option_value key =
  let (depr, _stage, (read,_,_)) = get_option key in
  let s = read () in
  match s with
    | BoolValue b ->
        Feedback.msg_notice Pp.(prlist_with_sep spc str key ++ str " is "
          ++ str (if b then "on" else "off"))
    | _ ->
        Feedback.msg_notice Pp.(str "Current value of "
          ++ prlist_with_sep spc str key ++ str " is " ++ msg_option_value s)

let get_tables () =
  let tables = !value_tab in
  let fold key (depr, _stage, (read,_,_)) accu =
    let state = {
      opt_depr = depr;
      opt_value = read ();
    } in
    OptionMap.add key state accu
  in
  OptionMap.fold fold tables OptionMap.empty

let print_tables () =
  let open Pp in
  let print_option key value depr =
    let msg = str "  " ++ str (nickname key) ++ str ": " ++ msg_option_value value in
    let depr = pr_opt (fun depr ->
        hov 2
          (str "[DEPRECATED" ++
           pr_opt (fun since -> str "since " ++ str since) depr.Deprecation.since ++
           pr_opt str depr.Deprecation.note ++
           str "]"))
        depr
    in
    msg ++ depr ++ fnl()
  in
  str "Options:" ++ fnl () ++
    OptionMap.fold
      (fun key (depr, _stage, (read,_,_)) p ->
        p ++ print_option key (read ()) depr)
      !value_tab (mt ()) ++
  str "Tables:" ++ fnl () ++
    List.fold_right
      (fun (nickkey,_) p -> p ++ str "  " ++ str nickkey ++ fnl ())
      !string_table (mt ()) ++
    List.fold_right
      (fun (nickkey,_) p -> p ++ str "  " ++ str nickkey ++ fnl ())
      !ref_table (mt ()) ++
    fnl ()
