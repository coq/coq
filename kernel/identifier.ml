(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id: *)


open Pp
open Util

(* Identifiers *)

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

(* This checks that a string is acceptable as an ident, i.e. starts
   with a letter and contains only letters, digits or "'" *)

let check_ident s =
  let l = String.length s in
  if l = 0 then error "The empty string is not an identifier"; 
  let c = String.get s 0 in
  if not (is_letter c) then error "An identifier starts with a letter";
  for i=1 to l-1 do
    let c = String.get s i in
    if not (is_letter c or is_digit c or c = '\'') then
      error
	("Character "^(String.sub s i 1)^" is not allowed in an identifier")
  done

let is_ident s = try check_ident s; true with _ -> false

module Identifier = struct

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

let has_index id = is_digit (id.[String.length id - 1])

let restart_ident id =
  let len = String.length id in
  let numstart = cut_ident id in
  let newid = String.make (numstart+1) '0' in
  String.blit id 0 newid 0 numstart;
  newid

let hash_sub hstr id = hstr id
let equal id1 id2 = id1 == id2

end (* End of module Identifier *)

type identifier = Identifier.t
let repr_ident = Identifier.repr_ident
let make_ident = Identifier.make_ident
let string_of_id = Identifier.string_of_id
let id_of_string = Identifier.id_of_string
let id_ord = Identifier.id_ord

module IdOrdered = 
  struct
    type t = identifier
    let compare = id_ord
  end

module Idset = Set.Make(IdOrdered)
module Idmap = Map.Make(IdOrdered)

let atompart_of_id id = fst (repr_ident id)
let index_of_id id = snd (repr_ident id)
let pr_id id = str (string_of_id id)

let first_char = Identifier.first_char

(* Fresh names *)

let lift_ident = Identifier.lift_ident

let next_ident_away id avoid = 
  if List.mem id avoid then
    let id0 = if not (Identifier.has_index id) then id else 
    (* Ce serait sans doute mieux avec quelque chose inspiré de 
       *** make_ident id (Some 0) *** mais ça brise la compatibilité... *)
    Identifier.restart_ident id in
    let rec name_rec id =
      if List.mem id avoid then name_rec (lift_ident id) else id in 
    name_rec id0
  else id

let next_ident_away_from id avoid = 
  let rec name_rec id =
    if List.mem id avoid then name_rec (lift_ident id) else id in 
  name_rec id 

let add_prefix s id = id_of_string (s^(string_of_id id))
let add_suffix id s = id_of_string ((string_of_id id)^s)

let wildcard = id_of_string "_"

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



(* Labels *)

type label=string

let string_of_label s = s
let label_of_string s = s

let pr_label l = str (string_of_label l) 

let ident_of_label l = l
let label_of_ident l = l

module Labset = Stringset
module Labmap = Stringmap

(* Unique idents *)


type uniq_ident = {name:string; stamp:int}

let current_stamp = ref 0

let unique s = incr current_stamp; {name=s; stamp= !current_stamp}
let rename uid = unique uid.name

let string_of_uid uid = uid.name
let pr_uid uid = str (string_of_uid uid) 

let debug_string_of_uid uid = uid.name^"_"^(string_of_int uid.stamp)
let debug_pr_uid uid = str (debug_string_of_uid uid) 

let compare_uids {name=n1; stamp=s1} {name=n2; stamp=s2} = 
  let c = compare s1 s2 in
    if c = 0 then
      compare n1 n2
    else
      c

module Umap = Map.Make(struct 
			 type t=uniq_ident 
			 let compare=compare_uids 
		       end)
