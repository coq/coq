(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util

(*s Identifiers *)

(* Utilities *)

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

(* Identifiers *)

type identifier = string

let cut_ident s =
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
  numpart slen slen

let repr_ident s =
  let slen = String.length s in
  let numstart = cut_ident s in
  if numstart = slen then 
    (s, None)
  else
    (String.sub s 0 numstart,
     Some (int_of_string (String.sub s numstart (slen - numstart))))

let make_ident sa = function
  | Some n -> 
      let c = Char.code (String.get sa (String.length sa -1)) in
      if c < code_of_0 or c > code_of_9 then sa ^ (string_of_int n)
      else sa ^ "_" ^ (string_of_int n)
  | None -> String.copy sa

let first_char id =
  assert (id <> "");
  String.make 1 id.[0]

let id_ord = Pervasives.compare

(* Rem: semantics is a bit different, if an ident starts with toto00 then
  after successive renamings it comes to toto09, then it goes on with toto10 *)
let lift_subscript id =
  let len = String.length id in
  let rec add carrypos =
    let c = id.[carrypos] in
    if is_digit c then
      if c = '9' then begin
	assert (carrypos>0);
	add (carrypos-1)
      end
      else begin
	let newid = String.copy id in
	String.fill newid (carrypos+1) (len-1-carrypos) '0';
	newid.[carrypos] <- Char.chr (Char.code c + 1);
	newid
      end
    else begin
      let newid = id^"0" in
      if carrypos < len-1 then begin
	String.fill newid (carrypos+1) (len-1-carrypos) '0';
	newid.[carrypos+1] <- '1'
      end;
      newid
    end
  in add (len-1)

let has_subscript id = is_digit (id.[String.length id - 1])

let forget_subscript id =
  let len = String.length id in
  let numstart = cut_ident id in
  let newid = String.make (numstart+1) '0' in
  String.blit id 0 newid 0 numstart;
  newid

(* This checks that a string is acceptable as an ident, i.e. starts
   with a letter and contains only letters, digits or "'" *)

let check_ident_suffix i l s =
  for i=1 to l-1 do
    let c = String.get s i in
    if not (is_letter c or is_digit c or c = '\'' or c = '_' or c = '@') then
      error
	("Character "^(String.sub s i 1)^" is not allowed in identifier "^s)
  done

let check_ident s =
  let l = String.length s in
  if l = 0 then error "The empty string is not an identifier";
  let c = String.get s 0 in
  if (is_letter c) or c = '_' or c = '$' or c = '?' 
  then check_ident_suffix 1 l s
  else error (s^": an identifier should start with a letter")

let is_ident s = try check_ident s; true with _ -> false

let check_suffix s = check_ident_suffix 0 (String.length s) s

let add_suffix id s = check_suffix s; id^s
let add_prefix s id = check_ident s; s^id

let string_of_id id = String.copy id
let id_of_string s = check_ident s; String.copy s

(* Hash-consing of identifier *)
module Hident = Hashcons.Make(
  struct 
    type t = string
    type u = string -> string
    let hash_sub hstr id = hstr id
    let equal id1 id2 = id1 == id2
    let hash = Hashtbl.hash
  end)

module IdOrdered = 
  struct
    type t = identifier
    let compare = id_ord
  end

module Idset = Set.Make(IdOrdered)
module Idmap = Map.Make(IdOrdered)

let atompart_of_id id = fst (repr_ident id)
let index_of_id id = snd (repr_ident id)
let pr_id id = [< 'sTR (string_of_id id) >]

let wildcard = id_of_string "_"

(* Fresh names *)

let lift_ident = lift_subscript

let next_ident_away id avoid = 
  if List.mem id avoid then
    let id0 = if not (has_subscript id) then id else 
    (* Ce serait sans doute mieux avec quelque chose inspiré de 
       *** make_ident id (Some 0) *** mais ça brise la compatibilité... *)
    forget_subscript id in
    let rec name_rec id =
      if List.mem id avoid then name_rec (lift_ident id) else id in 
    name_rec id0
  else id

let next_ident_away_from id avoid = 
  let rec name_rec id =
    if List.mem id avoid then name_rec (lift_ident id) else id in 
  name_rec id 

(* Names *)

type name = Name of identifier | Anonymous

let next_name_away_with_default default name l = 
  match name with
    | Name str  -> next_ident_away str l
    | Anonymous -> next_ident_away (id_of_string default) l

let next_name_away name l = 
  match name with
    | Name str  -> next_ident_away str l
    | Anonymous -> id_of_string "_"

let out_name = function
  | Name id -> id
  | Anonymous -> anomaly "out_name: expects a defined name"

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

(*s Directory paths = section names paths *)
type module_ident = identifier
type dir_path = module_ident list

module ModIdOrdered = 
  struct
    type t = identifier
    let compare = Pervasives.compare
  end

module ModIdmap = Map.Make(ModIdOrdered)

let make_dirpath x = x
let repr_dirpath x = x

let dirpath_prefix = function 
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | l -> snd (list_sep_last l)

let split_dirpath d = let (b,d) = list_sep_last d in (d,b)

let parse_sp s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try
      let pos = String.index_from s n '.' in
      let dir = String.sub s n (pos-n) in
      let dirs,n' = decoupe_dirs (succ pos) in
      (id_of_string dir)::dirs,n'
    with
      | Not_found -> [],n
  in
  if len = 0 then invalid_arg "parse_section_path";
  let dirs,n = decoupe_dirs 0 in
  let id = String.sub s n (len-n) in
  dirs, (id_of_string id)

let dirpath_of_string s =
  try
    let sl,s = parse_sp s in
    sl @ [s]
  with
    | Invalid_argument _ -> invalid_arg "dirpath_of_string"

let string_of_dirpath = function
  | [] -> "<empty>"
  | sl -> String.concat "." (List.map string_of_id sl)

let pr_dirpath sl = [< 'sTR (string_of_dirpath sl) >]

(*s Section paths are absolute names *)

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
let string_of_path sp =
  let (sl,id,k) = repr_path sp in
  if sl = [] then string_of_id id
  else (string_of_dirpath sl) ^ "." ^ (string_of_id id)

let path_of_string s =
  try
    let sl,s = parse_sp s in
    make_path sl s CCI
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_sp sp = [< 'sTR (string_of_path sp) >]

let sp_of_wd = function
  | [] -> invalid_arg "Names.sp_of_wd"
  | l -> let (bn,dp) = list_sep_last l in make_path dp bn OBJ

let wd_of_sp sp = 
  let (sp,id,_) = repr_path sp in sp @ [id]

let sp_ord sp1 sp2 =
  let (p1,id1,k) = repr_path sp1
  and (p2,id2,k') = repr_path sp2 in
  let ck = compare k k' in
  if ck = 0 then
    let p_bit = compare p1 p2 in
    if p_bit = 0 then id_ord id1 id2 else p_bit
  else
    ck

let is_dirpath_prefix_of = list_prefix_of

module SpOrdered =
  struct
    type t = section_path
    let compare = sp_ord
  end

module Spset = Set.Make(SpOrdered)

module Spmap = Map.Make(SpOrdered)

(* Special references for inductive objects *)

type variable_path = section_path
type constant_path = section_path
type inductive_path = section_path * int
type constructor_path = inductive_path * int
type mutual_inductive_path = section_path

(* Hash-consing of name objects *)
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
    type u = identifier -> identifier
    let hash_sub hident sp =
      { dirpath = List.map hident sp.dirpath;
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
  let hspcci = Hashcons.simple_hcons Hsp.f hident in
  let hspfw = Hashcons.simple_hcons Hsp.f hident in
  (hspcci,hspfw,hname,hident,hstring)
