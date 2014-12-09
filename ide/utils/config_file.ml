(*********************************************************************************)
(*                Cameleon                                                       *)
(*                                                                               *)
(*    Copyright (C) 2005 Institut National de Recherche en Informatique et       *)
(*    en Automatique. All rights reserved.                                       *)
(*                                                                               *)
(*    This program is free software; you can redistribute it and/or modify       *)
(*    it under the terms of the GNU Library General Public License as            *)
(*    published by the Free Software Foundation; either version 2 of the         *)
(*    License, or  any later version.                                            *)
(*                                                                               *)
(*    This program is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(*    GNU Library General Public License for more details.                       *)
(*                                                                               *)
(*    You should have received a copy of the GNU Library General Public          *)
(*    License along with this program; if not, write to the Free Software        *)
(*    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA                   *)
(*    02111-1307  USA                                                            *)
(*                                                                               *)
(*    Contact: Maxence.Guesdon@inria.fr                                          *)
(*                                                                               *)
(*********************************************************************************)

(* TODO *)
(* section comments *)
(* better obsoletes: no "{}", line cuts *)

(* possible improvements: *)
(* use lex/yacc instead of genlex to be more robust, efficient, allow arrays and other types, read comments. *)
(* description and help, level (beginner/advanced/...) for each cp *)
(* find an option from its name and group *)
(* class hooks *)
(* get the sections of a group / of a file *)
(* read file format from inifiles and ConfigParser *)


(* Read the mli before reading this file! *)


(* ******************************************************************************** *)
(* ******************************** misc utilities ******************************** *)
(* ******************************************************************************** *)
(* This code is intended to be usable without any dependencies. *)

(* pipeline style, see for instance Raw.of_channel. *)
let (|>) x f  = f x

(* as List.assoc, but applies f to the element matching [key] and returns the list
where this element has been replaced by the result of f. *)
let rec list_assoc_remove key f = function
  | [] -> raise Not_found
  | (key',value) as elt :: tail ->
      if key <> key'
      then elt :: list_assoc_remove key f tail
      else match f value with
        | None -> tail
        | Some a -> (key',a) :: tail

(* reminiscent of String.concat. Same as [Queue.iter f1 queue]
   but calls [f2 ()] between each calls to f1.
   Does not call f2 before the first call nor after the last call to f2.
   Could be more efficient with a richer module interface of Queue.
*)
let queue_iter_between f1 f2 queue =
(*   let f flag elt = if flag then f2 (); (f1 elt:unit); true in *)
  let f flag elt = if flag then f2 (); f1 elt; true in
  ignore (Queue.fold f false queue)

let list_iter_between f1 f2 = function
    [] -> ()
  | a::[] -> f1 a
  | a::tail -> f1 a; List.iter (fun elt -> (f2 ():unit); f1 elt) tail
(*   | a::tail -> f1 a; List.iter (fun elt -> f2 (); f1 elt) tail *)
(* !! types ??? *)

(* to ensure that strings will be parsed correctly by Genlex.
It's more comfortable not to have quotes around the string, but sometimes it's necessary. *)
exception Unsafe_string
let safe_string s =
  if s = ""
  then "\"\""
  else if (
    try match s.[0] with
      | 'a'..'z' | 'A'..'Z' ->
          for i = 1 to String.length s - 1 do
            match s.[i] with
                'a'..'z' | 'A'..'Z' | '_' | '0'..'9' -> ()
              | _ -> raise Unsafe_string
          done;
        false
      | _ ->
          try
            string_of_int (int_of_string s) <> s ||
            string_of_float (float_of_string s) <> s
          with Failure "int_of_string" | Failure "float_of_string" -> true
    with Unsafe_string -> true)
  then Printf.sprintf "\"%s\"" (String.escaped s)
  else s


(* ******************************************************************************** *)
(* ************************************* core ************************************* *)
(* ******************************************************************************** *)

module Raw = struct
  type cp =
    | String of string
    | Int of int
    | Float of float
    | List of cp list
    | Tuple of cp list
    | Section of (string * cp) list

(* code generated by
camlp4 pa_o.cmo pa_op.cmo pr_o.cmo -- -o config_file_parser.ml -impl config_file_parser.ml4
Unreadable on purpose, edit the file config_file_parser.ml4 rather than editing this (huge) lines. Then manually copy-paste here the content of config_file_parser.ml.
Could be one day rewritten with ocamllex/yacc to be more robust, efficient, allow arrays, read comments...*)
  module Parse = struct
    let lexer = Genlex.make_lexer ["="; "{"; "}"; "["; "]"; ";"; "("; ")"; ","]
    let rec file l (strm__ : _ Stream.t) = match try Some (ident strm__) with Stream.Failure -> None with Some id -> begin match Stream.peek strm__ with Some (Genlex.Kwd "=") -> Stream.junk strm__; let v = try value strm__ with Stream.Failure -> raise (Stream.Error "") in begin try file ((id, v) :: l) strm__ with Stream.Failure -> raise (Stream.Error "") end | _ -> raise (Stream.Error "") end | _ -> List.rev l
    and value (strm__ : _ Stream.t) = match Stream.peek strm__ with Some (Genlex.Kwd "{") -> Stream.junk strm__; let v = try file [] strm__ with Stream.Failure -> raise (Stream.Error "") in begin match Stream.peek strm__ with Some (Genlex.Kwd "}") -> Stream.junk strm__; Section v | _ -> raise (Stream.Error "") end | Some (Genlex.Ident s) -> Stream.junk strm__; String s | Some (Genlex.String s) -> Stream.junk strm__; String s | Some (Genlex.Int i) -> Stream.junk strm__; Int i | Some (Genlex.Float f) -> Stream.junk strm__; Float f | Some (Genlex.Char c) -> Stream.junk strm__; String (String.make 1 c) | Some (Genlex.Kwd "[") -> Stream.junk strm__; let v = try list [] strm__ with Stream.Failure -> raise (Stream.Error "") in List v | Some (Genlex.Kwd "(") -> Stream.junk strm__; let v = try list [] strm__ with Stream.Failure -> raise (Stream.Error "") in Tuple v | _ -> raise Stream.Failure
    and ident (strm__ : _ Stream.t) = match Stream.peek strm__ with Some (Genlex.Ident s) -> Stream.junk strm__; s | Some (Genlex.String s) -> Stream.junk strm__; s | _ -> raise Stream.Failure
    and list l (strm__ : _ Stream.t) = match Stream.peek strm__ with Some (Genlex.Kwd ";") -> Stream.junk strm__; begin try list l strm__ with Stream.Failure -> raise (Stream.Error "") end | Some (Genlex.Kwd ",") -> Stream.junk strm__; begin try list l strm__ with Stream.Failure -> raise (Stream.Error "") end | _ -> match try Some (value strm__) with Stream.Failure -> None with Some v -> begin try list (v :: l) strm__ with Stream.Failure -> raise (Stream.Error "") end | _ -> match Stream.peek strm__ with Some (Genlex.Kwd "]") -> Stream.junk strm__; List.rev l | Some (Genlex.Kwd ")") -> Stream.junk strm__; List.rev l | _ -> raise Stream.Failure
  end

  open Format
  (* formating convention: the caller has to open the box, close it and flush the output *)
  (* remarks on Format:
     set_margin forces a call to set_max_indent
     sprintf et bprintf are flushed at each call*)

  (* pretty print a Raw.cp *)
  let rec save formatter = function
    | String s -> fprintf formatter "%s" (safe_string s) (* How can I cut lines and *)
    | Int i -> fprintf formatter "%d" i             (* print backslashes just before the \n? *)
    | Float f -> fprintf formatter "%g" f
    | List l ->
        fprintf formatter "[@[<b0>";
        list_iter_between
          (fun v -> fprintf formatter "@[<b2>"; save formatter v; fprintf formatter "@]")
          (fun () -> fprintf formatter ";@ ")
          l;
        fprintf formatter "@]]"
    | Tuple l ->
        fprintf formatter "(@[<b0>";
        list_iter_between
          (fun v -> fprintf formatter "@[<b2>"; save formatter v; fprintf formatter "@]")
          (fun () -> fprintf formatter ",@ ")
          l;
        fprintf formatter "@])"
    | Section l ->
        fprintf formatter "{@;<0 2>@[<hv0>";
        list_iter_between
          (fun (name,value) ->
             fprintf formatter "@[<hov2>%s =@ @[<b2>" name;
             save formatter value;
             fprintf formatter "@]@]";)
          (fun () -> fprintf formatter "@;<2 0>")
          l;
        fprintf formatter "@]}"

(*   let to_string r = save str_formatter r; flush_str_formatter () *)
  let to_channel out_channel r =
    let f = formatter_of_out_channel out_channel in
    fprintf f "@[<b2>"; save f r; fprintf f "@]@?"

  let of_string s = s |> Stream.of_string |> Parse.lexer |> Parse.value

  let of_channel in_channel =
    let result = in_channel |> Stream.of_channel |> Parse.lexer |> Parse.file [] in
    close_in in_channel;
    result
end

(* print the given string in a way compatible with Format.
   Truncate the lines when needed, indent the newlines.*)
let print_help formatter =
  String.iter (function
   | ' ' -> Format.pp_print_space formatter ()
   | '\n' -> Format.pp_force_newline formatter ()
   | c -> Format.pp_print_char formatter c)

type 'a wrappers = {
 to_raw : 'a -> Raw.cp;
 of_raw : Raw.cp -> 'a}

class type ['a] cp = object
(*   method private to_raw = wrappers.to_raw *)
(*   method private of_raw = wrappers.of_raw *)
(*   method private set_string s = s |> Raw.of_string |> self#of_raw |> self#set *)
  method add_hook : ('a -> 'a -> unit) -> unit
  method get : 'a
  method get_default : 'a
  method set : 'a -> unit
  method reset : unit

  method get_formatted : Format.formatter -> unit
  method get_default_formatted : Format.formatter -> unit
  method get_help_formatted : Format.formatter -> unit

  method get_name : string list
  method get_short_name : string option
  method set_short_name : string -> unit
  method get_help : string
  method get_spec : Arg.spec

  method set_raw : Raw.cp -> unit
end

type groupable_cp = <
  get_name : string list;
  get_short_name : string option;
  get_help : string;

  get_formatted : Format.formatter -> unit;
  get_default_formatted : Format.formatter -> unit;
  get_help_formatted : Format.formatter -> unit;
  get_spec : Arg.spec;

  reset : unit;
  set_raw : Raw.cp -> unit; >

exception Double_name
exception Missing_cp of groupable_cp
exception Wrong_type of (out_channel -> unit)

(* Two exceptions to stop the iteration on queues. *)
exception Found
exception Found_cp of groupable_cp

(* The data structure to store the cps.
It's a tree, each node is a section, and a queue of sons with their name.
Each leaf contains a cp. *)
type 'a nametree =
  | Immediate of 'a
  | Subsection of ((string * 'a nametree) Queue.t)
      (* this Queue must be nonempty for group.read.choose *)

class group = object (self)
  val mutable cps = Queue.create () (* hold all the added cps, in a nametree. *)

  method add : 'a. 'a cp -> unit = fun original_cp ->
    let cp = (original_cp :> groupable_cp) in
    (* function called when we reach the end of the list cp#get_name. *)
    let add_immediate name cp queue =
      Queue.iter (fun (name',_) -> if name = name' then raise Double_name) queue;
      Queue.push (name, Immediate cp) queue in
    (* adds the cp with name [first_name::last_name] in section [section]. *)
    let rec add_in_section section first_name last_name cp queue =
      let sub_add = match last_name with (* what to do once we have find the correct section *)
        | [] -> add_immediate first_name
        | middle_name :: last_name -> add_in_section first_name middle_name last_name in
      try
        Queue.iter
          (function
             | name, Subsection subsection when name = section ->
                 sub_add cp subsection; raise Found
             | _ -> ())
          queue;
        let sub_queue = Queue.create () in
        sub_add cp sub_queue;
        Queue.push (section, Subsection sub_queue) queue
      with Found -> () in
    (match cp#get_name with
      | [] -> failwith "empty name"
      | first_name :: [] -> add_immediate first_name cp cps
      | first_name :: middle_name :: last_name ->
          add_in_section first_name middle_name last_name cp cps)

  method write ?(with_help=true) filename =
    let out_channel = open_out filename in
    let formatter = Format.formatter_of_out_channel out_channel in
    let print = Format.fprintf formatter in
    print "@[<v>";
    let rec save_queue formatter =
      queue_iter_between
        (fun (name,nametree) -> save_nametree name nametree)
        (Format.pp_print_cut formatter)
    and save_nametree name = function
      | Immediate cp ->
          if with_help && cp#get_help <> "" then
            (print "@[<hov3>(* "; cp#get_help_formatted formatter;
             print "@ *)@]@,");
          Format.fprintf formatter "@[<hov2>%s =@ @[<b2>" (safe_string name);
          cp#get_formatted formatter;
          print "@]@]"
      | Subsection queue ->
          Format.fprintf formatter "%s = {@;<0 2>@[<v>" (safe_string name);
          save_queue formatter queue;
          print "@]@,}" in
    save_queue formatter cps;
    print "@]@."; close_out out_channel

  method read ?obsoletes ?(no_default=false)
      ?(on_type_error = fun groupable_cp raw_cp output filename in_channel ->
          close_in in_channel;
          Printf.eprintf
            "Type error while loading configuration parameter %s from file %s.\n%!"
            (String.concat "." groupable_cp#get_name) filename;
          output stderr;
          exit 1)
      filename =
    (* [filename] is created if it doesn't exist. In this case there is no need to read it. *)
    match Sys.file_exists filename with false -> self#write filename | true ->
    let in_channel = open_in filename in
    (* what to do when a cp is missing: *)
    let missing cp default = if no_default then raise (Missing_cp cp) else default in
    (* returns a cp contained in the nametree queue, which must be nonempty *)
    let choose queue =
      let rec iter q = Queue.iter (function
        | _, Immediate cp -> raise (Found_cp cp)
        | _, Subsection q -> iter q) q in
      try iter queue; failwith "choose" with Found_cp cp -> cp in
    (* [set_and_remove raw_cps nametree] sets the cp of [nametree] to their value
       defined in [raw_cps] and returns the remaining raw_cps. *)
    let set_cp cp value =
      try cp#set_raw value
      with Wrong_type output -> on_type_error cp value output filename in_channel in
    let rec set_and_remove raw_cps = function
      | name, Immediate cp ->
          (try list_assoc_remove name (fun value -> set_cp cp value; None) raw_cps
           with Not_found -> missing cp raw_cps)
      | name, Subsection queue ->
          (try list_assoc_remove name
             (function
                | Raw.Section l ->
                    (match remainings l queue with
                       | [] -> None
                       | l -> Some (Raw.Section l))
                | r -> missing (choose queue) (Some r))
             raw_cps
           with Not_found -> missing (choose queue) raw_cps)
    and remainings raw_cps queue = Queue.fold set_and_remove raw_cps queue in
    let remainings = remainings (Raw.of_channel in_channel) cps in
    (* Handling of cps defined in filename but not belonging to self. *)
    if remainings <> [] then match obsoletes with
      | Some filename ->
          let out_channel =
            open_out filename in
(*             open_out_gen [Open_wronly; Open_creat; Open_append; Open_text] 0o666 filename in *)
          let formatter = Format.formatter_of_out_channel out_channel in
          Format.fprintf formatter "@[<v>";
          Raw.save formatter (Raw.Section remainings);
          Format.fprintf formatter "@]@.";
          close_out out_channel
      | None -> ()

  method command_line_args ~section_separator =
    let print = Format.fprintf Format.str_formatter in (* shortcut *)
    let result = ref [] in let push x = result := x :: !result in
    let rec iter = function
      | _, Immediate cp ->
          let key = "-" ^ String.concat section_separator cp#get_name in
          let spec = cp#get_spec in
          let doc = (
            print "@[<hv5>";
            Format.pp_print_as Format.str_formatter (String.length key +3) "";
            if cp#get_help <> ""
            then (print "@,@[<b2>"; cp#get_help_formatted Format.str_formatter; print "@]@ ")
            else print "@,";
            print "@[<hv>@[current:@;<1 2>@[<hov1>"; cp#get_formatted Format.str_formatter;
            print "@]@],@ @[default:@;<1 2>@[<b2>"; cp#get_default_formatted Format.str_formatter;
            print "@]@]@]@]";
            Format.flush_str_formatter ()) in
          (match cp#get_short_name with
            | None -> ()
            | Some short_name -> push ("-" ^ short_name,spec,""));
          push (key,spec,doc)
      | _, Subsection queue -> Queue.iter iter queue in
    Queue.iter iter cps;
    List.rev !result
end


(* Given wrappers for the type 'a, cp_custom_type defines a class 'a cp. *)
class ['a] cp_custom_type wrappers
  ?group:(group:group option) name ?short_name default help =
object (self)
  method private to_raw = wrappers.to_raw
  method private of_raw = wrappers.of_raw

  val mutable value = default
    (* output *)
  method get = value
  method get_default = default
  method get_formatted formatter = self#get |> self#to_raw |> Raw.save formatter
  method get_default_formatted formatter = self#get_default |> self#to_raw |> Raw.save formatter
    (* input *)
  method set v = let v' = value in value <- v; self#exec_hooks v' v
  method set_raw v = self#of_raw v |> self#set
  method private set_string s = s |> Raw.of_string |> self#of_raw |> self#set
  method reset = self#set self#get_default

  (* name *)
  val mutable shortname = short_name
  method get_name = name
  method get_short_name = shortname
  method set_short_name s = shortname <- Some s

  (* help *)
  method get_help = help
  method get_help_formatted formatter = print_help formatter self#get_help
  method get_spec = Arg.String self#set_string

  (* hooks *)
  val mutable hooks = []
  method add_hook f = hooks <- (f:'a->'a->unit) :: hooks
  method private exec_hooks v' v = List.iter (fun f -> f v' v) hooks

  initializer match group with Some g -> g#add (self :> 'a cp) | None -> ()
end


(* ******************************************************************************** *)
(* ****************************** predefined classes ****************************** *)
(* ******************************************************************************** *)

let int_wrappers = {
  to_raw = (fun v -> Raw.Int v);
  of_raw = function
    | Raw.Int v -> v
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Int expected, got %a\n%!" Raw.to_channel r))}
class int_cp ?group name ?short_name default help = object (self)
  inherit [int] cp_custom_type int_wrappers ?group name ?short_name default help
  method get_spec = Arg.Int self#set
end

let float_wrappers = {
  to_raw = (fun v -> Raw.Float v);
  of_raw = function
    | Raw.Float v -> v
    | Raw.Int v -> float v
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Float expected, got %a\n%!" Raw.to_channel r))
}
class float_cp ?group name ?short_name default help = object (self)
  inherit [float] cp_custom_type float_wrappers ?group name ?short_name default help
  method get_spec = Arg.Float self#set
end

(* The Pervasives version is too restrictive *)
let bool_of_string s =
  match String.lowercase s with
    | "false" | "no" | "n" | "0" -> false (* "0" and "1" aren't used. *)
    | "true" | "yes" | "y" | "1" -> true
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Bool expected, got %s\n%!" r))
let bool_wrappers = {
  to_raw = (fun v -> Raw.String (string_of_bool v));
  of_raw = function
    | Raw.String v -> bool_of_string v
    | Raw.Int v -> v <> 0
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Bool expected, got %a\n%!" Raw.to_channel r))
}
class bool_cp ?group name ?short_name default help = object (self)
  inherit [bool] cp_custom_type bool_wrappers ?group name ?short_name default help
  method get_spec = Arg.Bool self#set
end

let string_wrappers = {
  to_raw = (fun v -> Raw.String v);
  of_raw = function
    | Raw.String v -> v
    | Raw.Int v -> string_of_int v
    | Raw.Float v -> string_of_float v
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.String expected, got %a\n%!" Raw.to_channel r))
}
class string_cp ?group name ?short_name default help = object (self)
  inherit [string] cp_custom_type string_wrappers ?group name ?short_name default help
  method private of_string s = s
  method get_spec = Arg.String self#set
end

let list_wrappers wrappers = {
  to_raw = (fun l -> Raw.List (List.map wrappers.to_raw l));
  of_raw = function
    | Raw.List l -> List.map wrappers.of_raw l
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.List expected, got %a\n%!" Raw.to_channel r))
}
class ['a] list_cp wrappers = ['a list] cp_custom_type (list_wrappers wrappers)

let option_wrappers wrappers = {
  to_raw = (function
    | Some v -> wrappers.to_raw v
    | None -> Raw.String "");
  of_raw = function
    | Raw.String s as v -> (
        if s = "" || s = "None" then None
        else if String.length s >= 5 && String.sub s 0 5 = "Some "
        then Some (wrappers.of_raw (Raw.String (String.sub s 5 (String.length s -5))))
        else Some (wrappers.of_raw v))
    | r -> Some (wrappers.of_raw r)}
class ['a] option_cp wrappers = ['a option] cp_custom_type (option_wrappers wrappers)

let enumeration_wrappers enum =
  let switched = List.map (fun (string,cons) -> cons,string) enum in
  {to_raw = (fun v -> Raw.String (List.assq v switched));
   of_raw = function
     | Raw.String s ->
         (try List.assoc s enum
          with Not_found -> failwith (Printf.sprintf "%s isn't a known constructor" s))
     | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw enumeration expected, got %a\n%!" Raw.to_channel r))
}
class ['a] enumeration_cp enum ?group name ?short_name default help = object (self)
  inherit ['a] cp_custom_type (enumeration_wrappers enum)
    ?group name ?short_name default help
  method get_spec = Arg.Symbol (List.map fst enum, (fun s -> self#set (List.assoc s enum)))
end

let tuple2_wrappers wrapa wrapb = {
  to_raw = (fun (a,b) -> Raw.Tuple [wrapa.to_raw a; wrapb.to_raw b]);
  of_raw = function
    | Raw.Tuple [a;b] -> wrapa.of_raw a, wrapb.of_raw b
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Tuple 2 expected, got %a\n%!" Raw.to_channel r))
}
class ['a, 'b] tuple2_cp wrapa wrapb = ['a*'b] cp_custom_type (tuple2_wrappers wrapa wrapb)

let tuple3_wrappers wrapa wrapb wrapc = {
  to_raw = (fun (a,b,c) -> Raw.Tuple[wrapa.to_raw a; wrapb.to_raw b; wrapc.to_raw c]);
  of_raw = function
    | Raw.Tuple [a;b;c] -> wrapa.of_raw a, wrapb.of_raw b, wrapc.of_raw c
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Tuple 3 expected, got %a\n%!" Raw.to_channel r))
}
class ['a,'b,'c] tuple3_cp wrapa wrapb wrapc =
  ['a*'b*'c] cp_custom_type (tuple3_wrappers wrapa wrapb wrapc)

let tuple4_wrappers wrapa wrapb wrapc wrapd = {
  to_raw=(fun (a,b,c,d)->Raw.Tuple[wrapa.to_raw a;wrapb.to_raw b;wrapc.to_raw c;wrapd.to_raw d]);
  of_raw = function
    | Raw.Tuple [a;b;c;d] -> wrapa.of_raw a, wrapb.of_raw b, wrapc.of_raw c, wrapd.of_raw d
    | r -> raise (Wrong_type (fun outchan -> Printf.fprintf outchan
                                "Raw.Tuple 4 expected, got %a\n%!" Raw.to_channel r))
}
class ['a,'b,'c,'d] tuple4_cp wrapa wrapb wrapc wrapd =
  ['a*'b*'c*'d] cp_custom_type (tuple4_wrappers wrapa wrapb wrapc wrapd)

class string2_cp = [string,string] tuple2_cp string_wrappers string_wrappers
(* class color_cp = string_cp *)
class font_cp = string_cp
class filename_cp = string_cp


(* ******************************************************************************** *)
(******************** Backward compatibility with module Flags.****************** *)
(* ******************************************************************************** *)

type 'a option_class = 'a wrappers
type 'a option_record = 'a cp
type options_file = {mutable filename:string; group:group}

let create_options_file filename = {filename = filename; group = new group}
let set_options_file options_file filename = options_file.filename <- filename
let load {filename=f; group = g} = g#read f
let append {group=g} filename = g#read filename
let save {filename=f; group = g} = g#write ~with_help:false f
let save_with_help {filename=f; group = g} = g#write ~with_help:true f
let define_option {group=group} name help option_class default =
  (new cp_custom_type option_class ~group name default help)
let option_hook cp f = cp#add_hook (fun _ _ -> f ())

let  string_option = string_wrappers
let   color_option = string_wrappers
let    font_option = string_wrappers
let     int_option =    int_wrappers
let    bool_option =   bool_wrappers
let   float_option =  float_wrappers
let string2_option = tuple2_wrappers string_wrappers string_wrappers

let option_option = option_wrappers
let list_option = list_wrappers
let sum_option = enumeration_wrappers
let tuple2_option (a,b) = tuple2_wrappers a b
let tuple3_option (a,b,c) = tuple3_wrappers a b c
let tuple4_option (a,b,c,d) = tuple4_wrappers a b c d

let ( !! ) cp = cp#get
let ( =:= ) cp value = cp#set value

let shortname cp = String.concat ":" cp#get_name
let get_help cp = cp#get_help

type option_value =
  Module of option_module
| StringValue of  string
| IntValue of int
| FloatValue of float
| List of option_value list
| SmallList of option_value list
and option_module = (string * option_value) list

let rec value_to_raw = function
  | Module a -> Raw.Section (List.map (fun (name,value) -> name, value_to_raw value) a)
  | StringValue a -> Raw.String a
  | IntValue a -> Raw.Int a
  | FloatValue a -> Raw.Float a
  | List a -> Raw.List (List.map value_to_raw a)
  | SmallList a -> Raw.Tuple (List.map value_to_raw a)
let rec raw_to_value = function
  | Raw.String a -> StringValue a
  | Raw.Int a -> IntValue a
  | Raw.Float a -> FloatValue a
  | Raw.List a -> List (List.map raw_to_value a)
  | Raw.Tuple a -> SmallList (List.map raw_to_value a)
  | Raw.Section a -> Module (List.map (fun (name,value) -> name, raw_to_value value) a)

let define_option_class _ of_option_value to_option_value =
  {to_raw = (fun a -> a |> to_option_value |> value_to_raw);
   of_raw = (fun a -> a |> raw_to_value |> of_option_value)}

let to_value {to_raw = to_raw} a = a |> to_raw |> raw_to_value
let from_value {of_raw = of_raw} a = a |> value_to_raw |> of_raw

let of_value_w wrappers a = a |> value_to_raw |> wrappers.of_raw
let to_value_w wrappers a = a |> wrappers.to_raw |> raw_to_value
(* fancy indentation when finishing this stub code, not good style :-) *)
let value_to_string : option_value -> string = of_value_w string_option
let  string_to_value = to_value_w  string_option
let value_to_int     = of_value_w     int_option
let     int_to_value = to_value_w     int_option
let value_to_bool    = of_value_w    bool_option
let    bool_to_value = to_value_w    bool_option
let value_to_float   = of_value_w   float_option
let   float_to_value = to_value_w   float_option
let value_to_string2 = of_value_w string2_option
let string2_to_value = to_value_w string2_option
let value_to_list of_value =
  let wrapper = define_option_class "" of_value (fun _ -> failwith "value_to_list") in
  of_value_w (list_option wrapper)
let list_to_value to_value =
  let wrapper = define_option_class "" (fun _ -> failwith "value_to_list") to_value in
  to_value_w (list_option wrapper)
