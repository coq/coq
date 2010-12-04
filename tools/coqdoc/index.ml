(* -*- compile-command: "make -C ../.. bin/coqdoc" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Filename
open Lexing
open Printf
open Cdglobals

type loc = int

type entry_type =
  | Library
  | Module
  | Definition
  | Inductive
  | Constructor
  | Lemma
  | Record
  | Projection
  | Instance
  | Class
  | Method
  | Variable
  | Axiom
  | TacticDefinition
  | Abbreviation
  | Notation
  | Section

type index_entry =
  | Def of string * entry_type
  | Ref of coq_module * string * entry_type
  | Mod of coq_module * string

let current_type : entry_type ref = ref Library
let current_library = ref ""
  (** refers to the file being parsed *)

(** [deftable] stores only definitions and is used to interpolate idents
    inside comments, which are not globalized otherwise. *)

let deftable = Hashtbl.create 97

(** [reftable] stores references and definitions *)
let reftable = Hashtbl.create 97

let full_ident sp id =
  if sp <> "<>" then
    if id <> "<>" then
      sp ^ "." ^ id
    else sp
  else if id <> "<>"
  then id
  else ""

let add_def loc ty sp id =
  Hashtbl.add reftable (!current_library, loc) (Def (full_ident sp id, ty));
  Hashtbl.add deftable id (Ref (!current_library, full_ident sp id, ty))

let add_ref m loc m' sp id ty =
  if Hashtbl.mem reftable (m, loc) then ()
  else Hashtbl.add reftable (m, loc) (Ref (m', full_ident sp id, ty));
  let idx = if id = "<>" then m' else id in
    if Hashtbl.mem deftable idx then ()
    else Hashtbl.add deftable idx (Ref (m', full_ident sp id, ty))

let add_mod m loc m' id =
  Hashtbl.add reftable (m, loc) (Mod (m', id));
  Hashtbl.add deftable m (Mod (m', id))

let find m l = Hashtbl.find reftable (m, l)

let find_string m s = Hashtbl.find deftable s

(*s Manipulating path prefixes *)

type stack = string list

let rec string_of_stack st =
  match st with
    | [] -> ""
    | x::[] -> x
    | x::tl -> (string_of_stack tl) ^ "." ^ x

let empty_stack = []

let module_stack = ref empty_stack
let section_stack = ref empty_stack

let init_stack () =
  module_stack := empty_stack; section_stack := empty_stack

let push st p = st := p::!st
let pop st =
  match !st with
    | [] -> ()
    | _::tl -> st := tl

let head st =
  match st with
    | [] -> ""
    | x::_ -> x

let begin_module m = push module_stack m
let begin_section s = push section_stack s

let end_block id =
  (** determines if it ends a module or a section and pops the stack *)
  if ((String.compare (head !module_stack) id ) == 0) then
    pop module_stack
  else if ((String.compare (head !section_stack) id) == 0) then
    pop section_stack
  else
    ()

let make_fullid id =
  (** prepends the current module path to an id *)
  let path = string_of_stack !module_stack in
    if String.length path > 0 then
      path ^ "." ^ id
    else
      id


(* Coq modules *)

let split_sp s =
  try
    let i = String.rindex s '.' in
      String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1)
  with
      Not_found -> "", s

let modules = Hashtbl.create 97
let local_modules = Hashtbl.create 97

let add_module m =
  let _,id = split_sp m in
  Hashtbl.add modules id m;
  Hashtbl.add local_modules m ()

type module_kind = Local | External of string | Unknown

let external_libraries = ref []

let add_external_library logicalpath url =
  external_libraries := (logicalpath,url) :: !external_libraries

let find_external_library logicalpath =
  let rec aux = function
    | [] -> raise Not_found
    | (l,u)::rest ->
        if String.length logicalpath > String.length l &
          String.sub logicalpath 0 (String.length l + 1) = l ^"."
        then u
        else aux rest
  in aux !external_libraries

let init_coqlib_library () = add_external_library "Coq" !coqlib

let find_module m =
  if Hashtbl.mem local_modules m then
    Local
  else
    try External (Filename.concat (find_external_library m) m)
    with Not_found -> Unknown


(* Building indexes *)

type 'a index = {
  idx_name : string;
  idx_entries : (char * (string * 'a) list) list;
  idx_size : int }

let map f i =
  { i with idx_entries =
      List.map
	(fun (c,l) -> (c, List.map (fun (s,x) -> (s,f s x)) l))
	i.idx_entries }

let compare_entries (s1,_) (s2,_) = Alpha.compare_string s1 s2

let sort_entries el =
  let t = Hashtbl.create 97 in
  List.iter
    (fun c -> Hashtbl.add t c [])
    ['A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L'; 'M'; 'N';
     'O'; 'P'; 'Q'; 'R'; 'S'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z'; '_'; '*'];
  List.iter
    (fun ((s,_) as e) ->
      let c = Alpha.norm_char s.[0] in
      let c,l =
	try c,Hashtbl.find t c with Not_found -> '*',Hashtbl.find t '*' in
      Hashtbl.replace t c (e :: l))
    el;
  let res = ref [] in
  Hashtbl.iter (fun c l -> res := (c, List.sort compare_entries l) :: !res) t;
  List.sort (fun (c1,_) (c2,_) -> Alpha.compare_char c1 c2) !res

let display_letter c = if c = '*' then "other" else String.make 1 c

let index_size = List.fold_left (fun s (_,l) -> s + List.length l) 0

let hashtbl_elements h = Hashtbl.fold (fun x y l -> (x,y)::l) h []

let type_name = function
  | Library ->
      let ln = !lib_name in
        if ln <> "" then String.lowercase ln else "library"
  | Module -> "module"
  | Definition -> "definition"
  | Inductive -> "inductive"
  | Constructor -> "constructor"
  | Lemma -> "lemma"
  | Record -> "record"
  | Projection -> "projection"
  | Instance -> "instance"
  | Class -> "class"
  | Method -> "method"
  | Variable -> "variable"
  | Axiom -> "axiom"
  | TacticDefinition -> "tactic"
  | Abbreviation -> "abbreviation"
  | Notation -> "notation"
  | Section -> "section"

let prepare_entry s = function
  | Notation ->
      (* We decode the encoding done in Dumpglob.cook_notation of coqtop *)
      (* Encoded notations have the form section:sc:x_'++'_x where: *)
      (* - the section, if any, ends with a "." *)
      (* - the scope can be empty *)
      (* - tokens are separated with "_" *)
      (* - non-terminal symbols are conventionally represented by "x" *)
      (* - terminals are enclosed within simple quotes *)
      (* - existing simple quotes (that necessarily are parts of terminals) *)
      (*   are doubled *)
      (*   (as a consequence, when a terminal contains "_" or "x", these *)
      (*   necessarily appear enclosed within non-doubled simple quotes) *)
      (*   Example: "x ' %x _% y %'x %'_' z" is encoded as *)
      (*     "x_''''_'%x'_'_%'_x_'%''x'_'%''_'''_x" *)
      let err () = eprintf "Invalid notation in globalization file\n"; exit 1 in
      let h = try String.index_from s 0 ':' with _ -> err () in
      let i = try String.index_from s (h+1) ':' with _ -> err () in
      let sc = String.sub s (h+1) (i-h-1) in
      let ntn = String.make (String.length s - i) ' ' in
      let k = ref 0 in
      let j = ref (i+1) in
      let quoted = ref false in
      let l = String.length s - 1 in
      while !j <= l do
	if not !quoted then begin
	  (match s.[!j] with
	  | '_' -> ntn.[!k] <- ' '; incr k
	  | 'x' -> ntn.[!k] <- '_'; incr k
	  | '\'' -> quoted := true
	  | _ -> assert false)
	end
	else
	  if s.[!j] = '\'' then begin
	    if (!j = l || s.[!j+1] <> '\'') then quoted := false
	    else (ntn.[!k] <- s.[!j]; incr k; incr j)
	  end else begin
	    ntn.[!k] <- s.[!j];
	    incr k
	  end;
	incr j
      done;
      let ntn = String.sub ntn 0 !k in
      if sc = "" then ntn else ntn ^ " (" ^ sc ^ ")"
  | _ ->
      s

let all_entries () =
  let gl = ref [] in
  let add_g s m t = gl := (s,(m,t)) :: !gl in
  let bt = Hashtbl.create 11 in
  let add_bt t s m =
    let l = try Hashtbl.find bt t with Not_found -> [] in
      Hashtbl.replace bt t ((s,m) :: l)
  in
  let classify (m,_) e = match e with
    | Def (s,t) -> add_g s m t; add_bt t s m
    | Ref _ | Mod _ -> ()
  in
    Hashtbl.iter classify reftable;
    Hashtbl.iter (fun id m -> add_g id m Library; add_bt Library id m) modules;
    { idx_name = "global";
      idx_entries = sort_entries !gl;
      idx_size = List.length !gl },
    Hashtbl.fold (fun t e l -> (t, { idx_name = type_name t;
			             idx_entries = sort_entries e;
			             idx_size = List.length e }) :: l) bt []

let type_of_string = function
  | "def" | "coe" | "subclass" | "canonstruc" | "fix" | "cofix"
  | "ex" | "scheme" -> Definition
  | "prf" | "thm" -> Lemma
  | "ind" | "coind" -> Inductive
  | "constr" -> Constructor
  | "rec" | "corec" -> Record
  | "proj" -> Projection
  | "class" -> Class
  | "meth" -> Method
  | "inst" -> Instance
  | "var" -> Variable
  | "defax" | "prfax" | "ax" -> Axiom
  | "syndef" -> Abbreviation
  | "not" -> Notation
  | "lib" -> Library
  | "mod" | "modtype" -> Module
  | "tac" -> TacticDefinition
  | "sec" -> Section
  | s -> raise (Invalid_argument ("type_of_string:" ^ s))

let read_glob f =
  let c = open_in f in
  let cur_mod = ref "" in
  try
    while true do
      let s = input_line c in
      let n = String.length s in
      if n > 0 then begin
	match s.[0] with
	  | 'F' ->
	      cur_mod := String.sub s 1 (n - 1);
	      current_library := !cur_mod
	  | 'R' ->
	      (try
		Scanf.sscanf s "R%d:%d %s %s %s %s"
		  (fun loc1 loc2 lib_dp sp id ty ->
		    for loc=loc1 to loc2 do
		      add_ref !cur_mod loc lib_dp sp id (type_of_string ty)
		    done)
	       with _ ->
	       try
		Scanf.sscanf s "R%d %s %s %s %s"
		  (fun loc lib_dp sp id ty ->
		    add_ref !cur_mod loc lib_dp sp id (type_of_string ty))
	       with _ -> ())
	  | _ ->
	      try Scanf.sscanf s "%s %d %s %s"
		(fun ty loc sp id -> add_def loc (type_of_string ty) sp id)
	      with Scanf.Scan_failure _ -> ()
      end
    done; assert false
  with End_of_file ->
    close_in c
