
(* $Id$ *)

open Pp
open Names
open Univ
open Generic
open Term

let lexer = {
  Token.func = Lexer.func;
  Token.using = (fun _ -> ());
  Token.removing = (fun _ -> ());
  Token.tparse = Lexer.tparse;
  Token.text = Lexer.token_text }
  
type command =
  | Definition of identifier * constr option * constr
  | Parameter of identifier * constr
  | Variable of identifier * constr
  | Inductive of 
      (identifier * constr) list *
      (identifier * constr * (identifier * constr) list) list
  | Check of constr

let gram = Grammar.create lexer

let term = Grammar.Entry.create gram "term"
let name = Grammar.Entry.create gram "name"
let nametype = Grammar.Entry.create gram "nametype"
let inductive = Grammar.Entry.create gram "inductive"
let constructor = Grammar.Entry.create gram "constructor"
let command = Grammar.Entry.create gram "command"

let new_univ =
  let uc = ref 0 in
  let univ = id_of_string "univ" in
  fun () -> incr uc; { u_sp = make_path [] univ CCI; u_num = !uc }

let path_of_string s = make_path [] (id_of_string s) CCI

EXTEND
  name: 
  [ [ id = IDENT -> Name (id_of_string id)
    | "_" -> Anonymous
  ] ];
  nametype: 
  [ [ id = IDENT; ":"; t = term -> (id_of_string id, t) 
  ] ];
  term: 
  [ [ id = IDENT -> 
	VAR (id_of_string id) 
    | IDENT "Rel"; n = INT ->
	Rel (int_of_string n)
    | "Set" ->
	DOP0 (Sort (Prop Pos))
    | "Prop" ->
	DOP0 (Sort (Prop Null))
    | "Type" ->
	DOP0 (Sort (Type (new_univ())))
    | IDENT "Const"; id = IDENT ->
	DOPN (Const (path_of_string id), [||])
    | IDENT "Ind"; id = IDENT; n = INT ->
	let n = int_of_string n in
	DOPN (MutInd (path_of_string id, n), [||])
    | IDENT "Construct"; id = IDENT; n = INT; i = INT ->
	let n = int_of_string n and i = int_of_string i in
	DOPN (MutConstruct ((path_of_string id, n), i), [||])
    | "["; na = name; ":"; t = term; "]"; c = term ->
	DOP2 (Lambda, t, DLAM (na, c))
    | "("; na = name; ":"; t = term; ")"; c = term ->
	DOP2 (Prod, t, DLAM (na, c))
    | c1 = term; "->"; c2 = term ->
	DOP2 (Prod, c1, DLAM (Anonymous, c2))
    | "("; id = IDENT; cl = LIST1 term; ")" ->
	let c = VAR (id_of_string id) in
	DOPN (AppL, Array.of_list (c::cl))
    | "("; cl = LIST1 term; ")" ->
	begin match cl with
	  | [c] -> c
	  | _ -> DOPN (AppL, Array.of_list cl)
	end
    | "("; c = term; "::"; t = term; ")" ->
	DOP2 (Cast, c, t)
    | "<"; p = term; ">"; IDENT "Case"; c = term; "of"; 
      bl = LIST0 term; "end" ->
	DOPN (MutCase None, Array.of_list (p :: c :: bl))
  ] ];
  command: 
  [ [ "Definition"; id = IDENT; ":="; c = term; "." ->
	Definition (id_of_string id, None, c)
    | "Definition"; id = IDENT; ":"; t = term; ":="; c = term; "." ->
	Definition (id_of_string id, Some t, c)
    | "Parameter"; id = IDENT; ":"; t = term; "." ->
	Parameter (id_of_string id, t)
    | "Variable"; id = IDENT; ":"; t = term; "." ->
	Variable (id_of_string id, t)
    | "Inductive"; "["; params = LIST0 nametype SEP ";"; "]"; 
      inds = LIST1 inductive SEP "with" ->
	Inductive (params, inds)
    | IDENT "Check"; c = term; "." ->
	Check c
    | EOI -> raise End_of_file
  ] ];
  inductive: 
  [ [ id = IDENT; ":"; ar = term; ":="; constrs = LIST0 constructor SEP "|" ->
        (id_of_string id,ar,constrs)
  ] ];
  constructor:
  [ [ id = IDENT; ":"; c = term -> (id_of_string id,c) ] ];
END

(* Pretty-print. *)

let print_univers = ref false
let print_casts = ref false

let print_type u =
  let sp = u.u_sp and num = u.u_num in
  [< 'sTR "Type";
     if !print_univers then 
       [< 'sTR "("; print_id (basename sp); 'sPC; 'iNT num >] 
     else 
       [< >] 
  >]
  
let print_name = function
  | Anonymous -> [< 'sTR "_" >]
  | Name id -> print_id id

let print_rel bv n = print_name (List.nth bv (pred n))

let rename bv = function
  | Anonymous -> Anonymous
  | Name id as na -> 
      let idl = 
	List.fold_left 
	  (fun l n -> match n with Name x -> x::l | _ -> l) [] bv 
      in
      if List.mem na bv then Name (next_ident_away id idl) else na

let rec pp bv = function
  | DOP0 (Sort (Prop Pos)) -> [< 'sTR "Set" >]
  | DOP0 (Sort (Prop Null)) -> [< 'sTR "Prop" >]
  | DOP0 (Sort (Type u)) -> print_type u
  | DOP2 (Lambda, t, DLAM(na, c)) ->
      [< 'sTR"["; print_name na; 'sTR":"; pp bv t; 'sTR"]"; pp (na::bv) c >]
  | DOP2 (Prod, t, DLAM(na, c)) ->
      [< 'sTR"("; print_name na; 'sTR":"; pp bv t; 'sTR")"; pp (na::bv) c >]
  | DOP2 (Cast, c, t) ->
      if !print_casts then 
	[< 'sTR"("; pp bv c; 'sTR"::"; pp bv t; 'sTR")" >]
      else
	pp bv c
  | DOPN (AppL, cv) ->
      [< >]
  | DOPN (Const sp, _) ->
      [< 'sTR"Const "; print_id (basename sp) >]
  | DOPN (MutInd (sp,i), _) ->
      [< 'sTR"Ind "; print_id (basename sp); 'sTR" "; 'iNT i >]
  | DOPN (MutConstruct ((sp,i),j), _) ->
      [< 'sTR"Construct "; print_id (basename sp); 'sTR" "; 'iNT i; 
	 'sTR" "; 'iNT j >]
  | VAR id -> print_id id
  | Rel n -> print_rel bv n
  | _ -> [< 'sTR"<???>" >]

let pr_term = pp []
