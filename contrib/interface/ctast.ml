(* A copy of pre V7 ast *)

open Names
open Libnames

type loc = Util.loc

type t =
  | Node of loc * string * t list
  | Nvar of loc * string
  | Slam of loc * string option * t
  | Num of loc * int
  | Id of loc * string
  | Str of loc * string
  | Path of loc * string list
  | Dynamic of loc * Dyn.t

let section_path sl =
  match List.rev sl with
    | s::pa ->
	Libnames.encode_kn
	  (make_dirpath (List.map id_of_string pa))
	  (id_of_string s)
    | [] -> invalid_arg "section_path"

let is_meta s = String.length s > 0 && s.[0] == '$'

let purge_str s =
  if String.length s == 0 || s.[0] <> '$' then s
  else String.sub s 1 (String.length s - 1)

let rec ct_to_ast = function
  | Node (loc,a,b) -> Coqast.Node (loc,a,List.map ct_to_ast b)
  | Nvar (loc,a) ->
      if is_meta a then Coqast.Nmeta (loc,purge_str a)
      else Coqast.Nvar (loc,id_of_string a)
  | Slam (loc,Some a,b) ->
      if is_meta a then Coqast.Smetalam (loc,purge_str a,ct_to_ast b)
      else Coqast.Slam (loc,Some (id_of_string a),ct_to_ast b)
  | Slam (loc,None,b) -> Coqast.Slam (loc,None,ct_to_ast b)
  | Num (loc,a) -> Coqast.Num (loc,a)
  | Id (loc,a) -> Coqast.Id (loc,a)
  | Str (loc,a) -> Coqast.Str (loc,a)
  | Path (loc,sl) -> Coqast.Path (loc,section_path sl)
  | Dynamic (loc,a) -> Coqast.Dynamic (loc,a)

let rec ast_to_ct = function x -> failwith "ast_to_ct: not TODO?"
(*
  | Coqast.Node (loc,a,b) -> Node (loc,a,List.map ast_to_ct b)
  | Coqast.Nvar (loc,a) -> Nvar (loc,string_of_id a)
  | Coqast.Nmeta (loc,a) -> Nvar (loc,"$"^a)
  | Coqast.Slam (loc,Some a,b) ->
   Slam (loc,Some (string_of_id a),ast_to_ct b)
  | Coqast.Slam (loc,None,b) -> Slam (loc,None,ast_to_ct b)
  | Coqast.Smetalam (loc,a,b) -> Slam (loc,Some ("$"^a),ast_to_ct b)
  | Coqast.Num (loc,a) -> Num (loc,a)
  | Coqast.Id (loc,a) -> Id (loc,a)
  | Coqast.Str (loc,a) -> Str (loc,a)
  | Coqast.Path (loc,a) ->
    let (sl,bn) = Libnames.decode_kn a in
    Path(loc, (List.map string_of_id
                (List.rev (repr_dirpath sl))) @ [string_of_id bn])
  | Coqast.Dynamic (loc,a) -> Dynamic (loc,a)
*)

let loc = function
  | Node (loc,_,_) -> loc
  | Nvar (loc,_) -> loc
  | Slam (loc,_,_) -> loc
  | Num (loc,_) -> loc
  | Id (loc,_) -> loc
  | Str (loc,_) -> loc
  | Path (loc,_) -> loc
  | Dynamic (loc,_) -> loc

let str s = Str(Util.dummy_loc,s)
