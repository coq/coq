
(* $Id$ *)

open Pp
open Util

(* Utilities *)

let is_letter c =
  (c >= Char.code 'a' && c <= Char.code 'z') or
  (c >= Char.code 'A' && c <= Char.code 'Z') or
  (c >= Char.code '\248' && c <= Char.code '\255') or
  (c >= Char.code '\192' && c <= Char.code '\214') or
  (c >= Char.code '\216' && c <= Char.code '\246')

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

let is_digit c = (c >= code_of_0 && c <= code_of_9)


(* This checks that a string is acceptable as an ident, i.e. starts
   with a letter and contains only letters, digits or "'" *)

let check_ident s =
  let l = String.length s in
  if l = 0 then error "The empty string is not an identifier"; 
  let c = Char.code (String.get s 0) in
  if not (is_letter c) then error "An identifier starts with a letter";
  for i=1 to l-1 do
    let c = Char.code (String.get s i) in
    if not (is_letter c or is_digit c or c = Char.code '\'') then
      error
	("Character "^(String.sub s i 1)^" is not allowed in an identifier")
  done

let is_ident s = try check_ident s; true with _ -> false

(* Identifiers *)
(*
module Ident = struct

type t = {
  atom : string ; 
  index : int }

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

let first_char id =
  assert (id.atom <> "");
  String.make 1 id.atom.[0]

let id_ord { atom = s1; index = n1 } { atom = s2; index = n2 } = 
  let s_bit = Pervasives.compare s1 s2 in
  if s_bit = 0 then n1 - n2 else s_bit

(* Rem : if an ident starts with toto00 then after successive
   renamings it comes to toto09, then it goes on with toto010 *)
let lift_ident { atom = str; index = i } = { atom = str; index = i+1 }
let restart_ident id = { id with index = 0 }
let has_index id = (id.index <> -1)

let hash_sub hstr id = { atom = hstr id.atom; index = id.index }
let equal id1 id2 = id1.atom == id2.atom && id1.index = id2.index

end (* End of module Ident *)
*)
(* Second implementation *)
module Ident = struct

type t = string

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
  | None -> sa

let string_of_id id = id
let id_of_string s = s

let first_char id =
  assert (id <> "");
  String.make 1 id.[0]

let id_ord = Pervasives.compare

(* Rem: semantics is a bit different, if an ident starts with toto00 then
  after successive renamings it comes to toto09, then it goes on with toto10 *)
let lift_ident id =
  let len = String.length id in
  let rec add carrypos =
    let c = Char.code (id.[carrypos]) in
    if is_digit c then
      if c = code_of_9 then begin
	assert (carrypos>0);
	add (carrypos-1)
      end
      else begin
	let newid = String.copy id in
	String.fill newid (carrypos+1) (len-1-carrypos) '0';
	newid.[carrypos] <- Char.chr (c + 1);
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

let has_index id = is_digit (Char.code (id.[String.length id - 1]))

let restart_ident id =
  let len = String.length id in
  let numstart = cut_ident id in
  let newid = String.make (numstart+1) '0' in
  String.blit id 0 newid 0 numstart;
  newid

let hash_sub hstr id = hstr id
let equal id1 id2 = id1 == id2

end (* End of module Ident *)

type identifier = Ident.t
let repr_ident = Ident.repr_ident
let make_ident = Ident.make_ident
let string_of_id = Ident.string_of_id
let id_of_string = Ident.id_of_string
let id_ord = Ident.id_ord

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

let first_char = Ident.first_char

(* Fresh names *)

let lift_ident = Ident.lift_ident

let next_ident_away id avoid = 
  if List.mem id avoid then
    let id0 = if not (Ident.has_index id) then id else 
    (* Ce serait sans doute mieux avec quelque chose inspiré de 
       *** make_ident id (Some 0) *** mais ça brise la compatibilité... *)
    Ident.restart_ident id in
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

type qualid = string list * string

let make_qualid p s = (p,s)
let repr_qualid q = q

let string_of_qualid (l,s) = String.concat "." (l@[s])
let pr_qualid (l,s) = prlist_with_sep (fun () -> pr_str ".") pr_str (l@[s])

(*s Directory paths = section names paths *)
type dir_path = string list

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

let qualid_of_sp sp =
  make_qualid (dirpath sp) (string_of_id (basename sp))

(* parsing and printing of section paths *)
let string_of_dirpath sl = String.concat "." sl

let string_of_path sp =
  let (sl,id,k) = repr_path sp in
  String.concat ""
    (List.flatten (List.map (fun s -> [s;"."]) sl)
     @ [ string_of_id id ])

let parse_sp s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try
      let pos = String.index_from s n '.' in
      let dir = String.sub s n (pos-n) in
      let dirs,n' = decoupe_dirs (succ pos) in
      dir::dirs,n'
    with
      | Not_found -> [],n
  in
  if len = 0 then invalid_arg "parse_section_path";
  let dirs,n = decoupe_dirs 0 in
  let id = String.sub s n (len-n) in
  dirs,id

let path_of_string s =
  try
    let sl,s = parse_sp s in
    make_path sl (id_of_string s) CCI
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let dirpath_of_string s =
  try
    let sl,s = parse_sp s in
    sl @ [s]
  with
    | Invalid_argument _ -> invalid_arg "dirpath_of_string"

let pr_sp sp = [< 'sTR (string_of_path sp) >]

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

type constant_path = section_path
type inductive_path = section_path * int
type constructor_path = inductive_path * int

(* Hash-consing of identifier *)
module Hident = Hashcons.Make(
  struct 
    type t = Ident.t
    type u = string -> string
    let hash_sub = Ident.hash_sub
    let equal = Ident.equal
    let hash = Hashtbl.hash
  end)

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
