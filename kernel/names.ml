
(* $Id$ *)

open Pp
open Util

(* Identifiers *)

type identifier = {
  atom : string ; 
  index : int }

type name = Name of identifier | Anonymous

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

let repr_ident { atom = sa; index = n } =
  if n = -1 then (sa,None) else (sa,Some n)

let make_ident sa = function
  | Some n ->
      let c = Char.code (String.get sa (String.length sa -1)) in
      if c < code_of_0 or c > code_of_9 then { atom = sa; index = n }
      else { atom = sa^"_"; index = n }
  | None -> { atom = sa; index = -1 }

let string_of_id id = match repr_ident id with
  | (s,None) -> s
  | (s,Some n) -> s ^ (string_of_int n)

let id_of_string s =
  let slen = String.length s in
  (* [n'] is the position of the first non nullary digit *)
  let rec numpart n n' =
    if n = 0 then 
      failwith
	("The string " ^ s ^ " is not an identifier: it contains only digits")
    else 
      let c = Char.code (String.get s (n-1)) in
      if c = code_of_0 && n <> slen then 
	numpart (n-1) n' 
      else if code_of_0 <= c && c <= code_of_9 then 
	numpart (n-1) (n-1)
      else 
	n'
  in
  let numstart = numpart slen slen in
  if numstart = slen then 
    { atom = s; index = -1 } 
  else
    { atom = String.sub s 0 numstart;
      index = int_of_string (String.sub s numstart (slen - numstart)) }

let atompart_of_id id = id.atom
let index_of_id id = snd (repr_ident id)

let print_id id =
  match repr_ident id with
    | ("",None)   -> [< 'sTR"[]" >]
    | ("",Some n) -> [< 'sTR"[" ; 'iNT n ; 'sTR"]" >]
    | (s,None)   -> [< 'sTR s >]
    | (s,Some n) -> [< 'sTR s ; 'iNT n >]

let id_ord { atom = s1; index = n1 } { atom = s2; index = n2 } = 
  let s_bit = Pervasives.compare s1 s2 in
  if s_bit = 0 then n1 - n2 else s_bit

let first_char id =
  if id.atom = "" then
    failwith "lowercase_first_char"
  else
    String.make 1 id.atom.[0]

module IdOrdered = 
  struct
    type t = identifier
    let compare = id_ord
  end

module Idset = Set.Make(IdOrdered)
module Idmap = Map.Make(IdOrdered)


(* Fresh names *)
let lift_ident { atom = str; index = i } = { atom = str; index = i+1 }

let next_ident_away id avoid = 
  if List.mem id avoid then
    let id0 = if id.index = -1 then id else 
    (* Ce serait sans doute mieux avec quelque chose inspiré de 
       *** make_ident id (Some 0) *** mais ça brise la compatibilité... *)
    { id with index = -1 } in
    let rec name_rec id =
      if List.mem id avoid then name_rec (lift_ident id) else id in 
    name_rec id0
  else id

let next_ident_away_from id avoid = 
  let rec name_rec id =
    if List.mem id avoid then name_rec (lift_ident id) else id in 
  name_rec id 

let next_name_away_with_default default name l = 
  match name with
    | Name str  -> next_ident_away str l
    | Anonymous -> next_ident_away (id_of_string default) l

let next_name_away name l = 
  match name with
    | Name str  -> next_ident_away str l
    | Anonymous -> id_of_string "_"

(* Kinds *)

type path_kind = CCI | FW | OBJ

let string_of_kind = function
  | CCI -> "cci" 
  | FW -> "fw" 
  | OBJ -> "obj"

let kind_of_string = function
  | "cci" -> CCI 
  | "fw" -> FW 
  | "obj" -> OBJ
  | _ -> invalid_arg "kind_of_string"


(*s Section paths *)

type dir_path = string list

type section_path = {
  dirpath : dir_path ;
  basename : identifier ;
  kind : path_kind }

let make_path pa id k = { dirpath = pa; basename = id; kind = k }
let repr_path { dirpath = pa; basename = id; kind = k} = (pa,id,k)

let kind_of_path sp = sp.kind
let basename sp = sp.basename
let dirpath sp = sp.dirpath

(* parsing and printing of section paths *)
let string_of_dirpath sl = String.concat "#" (""::sl)

let string_of_path sp =
  let (sl,id,k) = repr_path sp in
  String.concat ""
    ((List.flatten (List.map (fun s -> ["#";s]) sl))
     @ [ "#"; string_of_id id; "."; string_of_kind k ])
    
let path_of_string s =
  try
    let (sl,s,k) = parse_section_path s in
    make_path sl (id_of_string s) (kind_of_string k)
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let print_sp sp = [< 'sTR (string_of_path sp) >]

let sp_of_wd = function
  | [] -> invalid_arg "Names.sp_of_wd"
  | l -> let (bn,dp) = list_sep_last l in make_path dp (id_of_string bn) OBJ

let wd_of_sp sp = 
  let (sp,id,_) = repr_path sp in sp @ [string_of_id id]

let sp_ord sp1 sp2 =
  let (p1,id1,k) = repr_path sp1
  and (p2,id2,k') = repr_path sp2 in
  let ck = compare k k' in
  if ck = 0 then
    let p_bit = compare p1 p2 in
    if p_bit = 0 then id_ord id1 id2 else p_bit
  else
    ck

let dirpath_prefix_of = list_prefix_of

module SpOrdered =
  struct
    type t = section_path
    let compare = sp_ord
  end

module Spset = Set.Make(SpOrdered)

module Spmap = Map.Make(SpOrdered)

(* Special references for inductive objects *)

type inductive_path = section_path * int
type constructor_path = inductive_path * int

(* Hash-consing of name objects *)
module Hident = Hashcons.Make(
  struct 
    type t = identifier
    type u = string -> string
    let hash_sub hstr id =
      { atom = hstr id.atom; index = id.index }
    let equal id1 id2 = id1.atom == id2.atom && id1.index = id2.index
    let hash = Hashtbl.hash
  end)

module Hname = Hashcons.Make(
  struct 
    type t = name
    type u = identifier -> identifier
    let hash_sub hident = function
      | Name id -> Name (hident id)
      | n -> n
    let equal n1 n2 =
      match (n1,n2) with
	| (Name id1, Name id2) -> id1 == id2
        | (Anonymous,Anonymous) -> true
        | _ -> false
    let hash = Hashtbl.hash
  end)

module Hsp = Hashcons.Make(
  struct 
    type t = section_path
    type u = (identifier -> identifier) * (string -> string)
    let hash_sub (hident,hstr) sp =
      { dirpath = List.map hstr sp.dirpath;
        basename = hident sp.basename;
        kind = sp.kind }
    let equal sp1 sp2 =
      (sp1.basename == sp2.basename) && (sp1.kind = sp2.kind)
      && (List.length sp1.dirpath = List.length sp2.dirpath)
      && List.for_all2 (==) sp1.dirpath sp2.dirpath
    let hash = Hashtbl.hash
  end)

let hcons_names () =
  let hstring = Hashcons.simple_hcons Hashcons.Hstring.f () in
  let hident = Hashcons.simple_hcons Hident.f hstring in
  let hname = Hashcons.simple_hcons Hname.f hident in
  let hspcci = Hashcons.simple_hcons Hsp.f (hident,hstring) in
  let hspfw = Hashcons.simple_hcons Hsp.f (hident,hstring) in
  (hspcci,hspfw,hname,hident,hstring)
