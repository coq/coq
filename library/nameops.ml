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
open Names
open Declarations
open Environ
open Term

(* Identifiers *)

let pr_id id = [< 'sTR (string_of_id id) >]

let wildcard = id_of_string "_"

(* Utilities *)

let code_of_0 = Char.code '0'
let code_of_9 = Char.code '9'

let cut_ident s =
  let s = string_of_id s in
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
  let numstart = cut_ident s in
  let s = string_of_id s in
  let slen = String.length s in
  if numstart = slen then 
    (s, None)
  else
    (String.sub s 0 numstart,
     Some (int_of_string (String.sub s numstart (slen - numstart))))

let make_ident sa = function
  | Some n -> 
      let c = Char.code (String.get sa (String.length sa -1)) in
      let s =
        if c < code_of_0 or c > code_of_9 then sa ^ (string_of_int n)
        else sa ^ "_" ^ (string_of_int n) in
      id_of_string s
  | None -> id_of_string (String.copy sa)

(* Rem: semantics is a bit different, if an ident starts with toto00 then
  after successive renamings it comes to toto09, then it goes on with toto10 *)
let lift_subscript id =
  let id = string_of_id id in
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
  in id_of_string (add (len-1))

let has_subscript id =
  let id = string_of_id id in
  is_digit (id.[String.length id - 1])

let forget_subscript id =
  let numstart = cut_ident id in
  let newid = String.make (numstart+1) '0' in
  String.blit (string_of_id id) 0 newid 0 numstart;
  (id_of_string newid)

let add_suffix id s = id_of_string (string_of_id id ^ s)
let add_prefix s id = id_of_string (s ^ string_of_id id)

let atompart_of_id id = fst (repr_ident id)

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

let out_name = function
  | Name id -> id
  | Anonymous -> anomaly "out_name: expects a defined name"

let next_name_away_with_default default name l = 
  match name with
    | Name str  -> next_ident_away str l
    | Anonymous -> next_ident_away (id_of_string default) l

let next_name_away name l = 
  match name with
    | Name str  -> next_ident_away str l
    | Anonymous -> id_of_string "_"

(**********************************************)

let pr_dirpath sl = [< 'sTR (string_of_dirpath sl) >]

(* Operations on dirpaths *)
let empty_dirpath = make_dirpath []

let default_module_name = id_of_string "Top"
let default_module = make_dirpath [default_module_name]

(*s Roots of the space of absolute names *)
let coq_root = id_of_string "Coq"
let default_root_prefix = make_dirpath []

let restrict_path n sp =
  let dir, s = repr_path sp in
  let (dir',_) = list_chop n (repr_dirpath dir) in
  Names.make_path (make_dirpath dir') s

(* Pop the last n module idents *)
let extract_dirpath_prefix n dir =
  let (_,dir') = list_chop n (repr_dirpath dir) in
  make_dirpath dir'

let dirpath_prefix p = match repr_dirpath p with
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | _::l -> make_dirpath l

let is_dirpath_prefix_of d1 d2 =
  list_prefix_of (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))

(* To know how qualified a name should be to be understood in the current env*)
let add_dirpath_prefix id d = make_dirpath (repr_dirpath d @ [id])

let split_dirpath d =
  let l = repr_dirpath d in (make_dirpath (List.tl l), List.hd l)

let extend_dirpath p id = make_dirpath (id :: repr_dirpath p)


(* Section paths *)

let dirpath sp = let (p,_) = repr_path sp in p
let basename sp = let (_,id) = repr_path sp in id

let path_of_constructor env ((sp,tyi),ind) =
   let mib = Environ.lookup_mind sp env in
   let mip = mib.mind_packets.(tyi) in 
   let (pa,_) = repr_path sp in 
   Names.make_path pa (mip.mind_consnames.(ind-1))

let path_of_inductive env (sp,tyi) =
  if tyi = 0 then sp
  else
    let mib = Environ.lookup_mind sp env in
    let mip = mib.mind_packets.(tyi) in 
    let (pa,_) = repr_path sp in 
    Names.make_path pa (mip.mind_typename) 

(* parsing *)
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
  make_dirpath (List.rev dirs), (id_of_string id)

let dirpath_of_string s =
  try
    let sl,s = parse_sp s in
    extend_dirpath sl s
  with
    | Invalid_argument _ -> invalid_arg "dirpath_of_string"

let path_of_string s =
  try
    let sl,s = parse_sp s in
    make_path sl s
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

(* Section paths *)
let pr_sp sp = [< 'sTR (string_of_path sp) >]
