
(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Declarations
open Environ
open Reduction
open Miniml
open Mlimport

(*s Renaming issues. We distinguish between globals and locals. A global table
    keeps the renamings of globals. And the functor argument will provide
    functions to renamed other identifiers. *)

(* We keep a table of renamings for the globals.
   Then every renaming function will be called with its own "avoid list"
   and the list of already known globals. *)

let globals_renaming = ref ([] : (identifier * identifier) list)

let globals = ref ([] : identifier list)

let reset_globals_renaming () =
  globals_renaming := [] ;
  globals          := []

let add_global_renaming ((_,id') as r) = 
  globals_renaming :=   r::!globals_renaming ;
  globals          := id'::!globals

let get_global_name id =
  try  List.assoc id !globals_renaming
  with Not_found -> anomalylabstrm "Fwtoml.get_global_name"
    (hOV 0 [< 'sTR "Found a global " ; pr_id id ;
              'sTR " without renaming" >])

(*s Informations on inductive types: we keep them in a table in order
    to have quick access to constructor names and arities. *)

type packet_info = { 
  packet_name    : identifier ;
  packet_ncons   : int ;
  packet_cnames  : identifier array ;
  packet_arities : int array }

let mind_table =
  (Hashtbl.create 17 : (section_path * int , packet_info) Hashtbl.t)

let reset_mind_table () =
  Hashtbl.clear mind_table

let store_mind_info key info =
  Hashtbl.add mind_table key info

let get_mind_info key =
  Hashtbl.find mind_table key

(*s [name_of_oper] returns the ML name of a global reference. *)

let name_of_oper gr =
  if is_ml_import gr then
    find_ml_import gr
  else if is_ml_extract gr then
    find_ml_extract gr
  else match gr with
    | ConstRef sp -> 
	get_global_name (basename sp)
    | IndRef ind ->
	let info = get_mind_info ind in info.packet_name
    | ConstructRef (ind,j) ->
	let info = get_mind_info ind in info.packet_cnames.(j-1)
    | VarRef _ -> 
	assert false

(* Other renaming functions are provided within the functor argument. *)

type renaming_function = identifier list -> name -> identifier

module type Renaming = sig
  val rename_type_parameter : renaming_function
  val rename_type : renaming_function
  val rename_term : renaming_function
  val rename_global_type : renaming_function
  val rename_global_constructor : renaming_function
  val rename_global_term : renaming_function
end

(*s The extraction functor. *)

module type Translation = sig
  val extract : bool -> global_reference list -> ml_decl list
end

module Make = functor (R : Renaming) -> struct

  (* The renaming functions must take globals into account *)

  let ren_type_parameter av n = R.rename_type_parameter (!globals @ av) n
  let ren_type av n = R.rename_type (!globals @ av) n
  let ren_term av n = R.rename_term (!globals @ av) n
				  
  let ren_global_type id = R.rename_global_type !globals (Name id)
  let ren_global_constructor i = R.rename_global_constructor !globals (Name i)
  let ren_global_term id = R.rename_global_term !globals (Name id)

  (* Extraction of a type *)

  let prop = id_of_string "prop"

  type type_extraction =
    | MLtype of ml_type * ml_typeid list * ml_typeid list
    | Arity

  let extract_type c =
    let rec extract_rec env pl fl c args = match kind_of_term (whd_beta c) with
      | IsProd (n, t, d) ->
	  assert (args = []);
	  let env' = push_rel (n,None,t) env in
	  (match extract_rec env pl fl t [] with
	     | Arity ->
		 let id = ren_type_parameter pl n in
		 extract_rec env' (id :: pl) fl d []
	     | MLtype (t', pl', fl') ->
		 (match extract_rec env' pl' fl' d [] with
		    | Arity -> Arity
		    | MLtype (d', pl'', fl'') -> 
			MLtype (Tarr (t', d'), pl'', fl'')))
      | IsSort (Prop Null) ->
	  assert (args = []);
	  MLtype (Tglob prop, [], [])
      | IsSort _ ->
	  assert (args = []);
	  Arity
      | IsApp (d, args') ->
	  extract_rec env pl fl d (Array.to_list args' @ args)
      | _ -> 
	  assert false
    in
    extract_rec (Global.env()) [] [] c []

  (* Extraction of a constr *)

  let extract_constr c = 
    let rec extract_rec env c = match kind_of_term (whd_beta c) with
      | _ -> 
	  failwith "todo"
      | IsSort _ | IsXtra _ | IsVar _ | IsMeta _ ->
          assert false 
    in
    extract_rec (Global.env()) c

  (* Extraction of a constant *)

  let extract_constant sp cb =
    let id = basename sp in
    let typ = cb.const_type in
    let redtyp = whd_betadeltaiota (Global.env()) Evd.empty typ in
    let body = match cb.const_body with Some c -> c | None -> assert false in
    if isSort redtyp then begin
      let id' = ren_global_type id in
      add_global_renaming (id,id');
      if is_Prop redtyp then
	Dabbrev (id', [], Tglob prop)
      else
	match extract_type body with
	  | Arity -> error "not an ML type"
	  | MLtype (t, vl, fl) -> Dabbrev (id', vl@fl, t)
    end else begin
      let id' = ren_global_term id in
      add_global_renaming (id,id'); 
      let t = extract_constr body in
      Dglob (id', t)
    end
      
  (* Extraction of an inductive *)

  let extract_inductive mib =
    failwith "todo"
    (* Dtype ... *)

  (* Extraction of a declaration i.e. a constant or an inductive *)

  let extract_decl = function
    | ConstRef sp -> extract_constant sp (Global.lookup_constant sp)
    | IndRef (sp,_) -> extract_inductive (Global.lookup_mind sp)
    | VarRef _ | ConstructRef _ -> assert false

  let extract cofix = List.map extract_decl

end
