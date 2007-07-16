(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo" i*)

(* $Id$ *)

open Pp
open Util
open Names
open Univ
open Term
open Environ

let lexer =
  {Token.func = Lexer.func; Token.using = Lexer.add_token;
   Token.removing = (fun _ -> ()); Token.tparse = Lexer.tparse;
   Token.text = Lexer.token_text}
;;

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

let path_of_string s = make_path [] (id_of_string s)

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
	mkVar (id_of_string id) 
    | IDENT "Rel"; n = INT ->
	mkRel (int_of_string n)
    | "Set" ->
	mkSet
    | "Prop" ->
	mkProp
    | "Type" ->
	mkType (new_univ())
    | "Const"; id = IDENT ->
	mkConst (path_of_string id, [||])
    | "Ind"; id = IDENT; n = INT ->
	let n = int_of_string n in
	mkMutInd ((path_of_string id, n), [||])
    | "Construct"; id = IDENT; n = INT; i = INT ->
	let n = int_of_string n and i = int_of_string i in
	mkMutConstruct (((path_of_string id, n), i), [||])
    | "["; na = name; ":"; t = term; "]"; c = term ->
	mkLambda (na,t,c)
    | "("; na = name; ":"; t = term; ")"; c = term ->
	mkProd (na,t,c)
    | c1 = term; "->"; c2 = term ->
	mkArrow c1 c2
    | "("; id = IDENT; cl = LIST1 term; ")" ->
	let c = mkVar (id_of_string id) in
	mkApp (c, Array.of_list cl)
    | "("; cl = LIST1 term; ")" ->
	begin match cl with
	  | [c] -> c
	  | c::cl -> mkApp (c, Array.of_list cl)
	end
    | "("; c = term; "::"; t = term; ")" ->
	mkCast (c, t)
    | "<"; p = term; ">"; 
	IDENT "Case"; c = term; ":"; "Ind"; id = IDENT; i = INT;
	"of"; bl = LIST0 term; "end" ->
	  let ind = (path_of_string id,int_of_string i) in
	  let nc = List.length bl in
	  let dummy_pats = Array.create nc RegularPat in
	  let dummy_ci = [||],(ind,[||],nc,None,dummy_pats) in
	  mkMutCase (dummy_ci, p, c, Array.of_list bl)
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
  if !print_univers then (str "Type" ++ pr_uni u)
  else (str "Type")

let print_name = function
  | Anonymous -> (str "_")
  | Name id -> pr_id id

let print_rel bv n = print_name (List.nth bv (pred n))

let rename bv = function
  | Anonymous -> Anonymous
  | Name id as na -> 
      let idl = 
	List.fold_left 
	  (fun l n -> match n with Name x -> x::l | _ -> l) [] bv 
      in
      if List.mem na bv then Name (next_ident_away id idl) else na

let rec pp bv t =
  match kind_of_term t with
  | Sort (Prop Pos) -> (str "Set")
  | Sort (Prop Null) -> (str "Prop")
  | Sort (Type u) -> print_type u
  | Lambda (na, t, c) ->
      (str"[" ++ print_name na ++ str":" ++ pp bv t ++ str"]" ++ pp (na::bv) c)
  | Prod (Anonymous, t, c) ->
      (pp bv t ++ str"->" ++ pp (Anonymous::bv) c)
  | Prod (na, t, c) ->
      (str"(" ++ print_name na ++ str":" ++ pp bv t ++ str")" ++ pp (na::bv) c)
  | Cast (c, t) ->
      if !print_casts then 
	(str"(" ++ pp bv c ++ str"::" ++ pp bv t ++ str")")
      else 
	pp bv c
  | App(h, v) ->
      (str"(" ++ pp bv h ++ spc () ++
         prvect_with_sep (fun () -> (spc ())) (pp bv) v ++ str")")
  | Const (sp, _) ->
      (str"Const " ++ pr_id (basename sp))
  | Ind ((sp,i), _) ->
      (str"Ind " ++ pr_id (basename sp) ++ str" " ++ int i)
  | Construct (((sp,i),j), _) ->
      (str"Construct " ++ pr_id (basename sp) ++ str" " ++ int i ++ 
	 str" " ++ int j)
  | Var id -> pr_id id
  | Rel n -> print_rel bv n
  | _ -> (str"<???>")

let pr_term _ ctx = pp (fold_rel_context (fun _ (n,_,_) l -> n::l) ctx [])

