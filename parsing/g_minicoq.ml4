(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Util
open Identifier
open Names
open Univ
open Term
open Declarations
open Mod_declarations
open Environ

let lexer = {
  Token.func = Lexer.func;
  Token.using = Lexer.add_token;
  Token.removing = (fun _ -> ());
  Token.tparse = Lexer.tparse;
  Token.text = Lexer.token_text }

(* This type is necessary for interactive modules *)
type declaration = 
  | Value of label * constr option * constr option
  | Inductive of (identifier * constr) list *
      (label * constr * (label * constr) list) list
  | Module of label * (mod_bound_id * module_type_entry) list * 
      module_type_entry option * module_expr option
  | ModuleType of label * module_type_entry

type command =
  | Entry of (label * specification_entry)
  | BeginModule of label * (mod_bound_id * module_type_entry) list * 
      module_type_entry option
  | EndModule of label
  | Check of constr
  | Abbrev of identifier * constr
  | Print of long_name
  | Reduce of constr

let gram = Grammar.create lexer

let term = Grammar.Entry.create gram "term"
let name = Grammar.Entry.create gram "name"
let longident = Grammar.Entry.create gram "longident"
let nametype = Grammar.Entry.create gram "nametype"
let inductive = Grammar.Entry.create gram "inductive"
let constructor = Grammar.Entry.create gram "constructor"
let command = Grammar.Entry.create gram "command"
let module_type = Grammar.Entry.create gram "module_type"
let module_type_decl = Grammar.Entry.create gram "module_type_decl"
let module_arg = Grammar.Entry.create gram "module_arg"
let module_expr = Grammar.Entry.create gram "module_expr"
let module_body_decl = Grammar.Entry.create gram "module_body_decl"
let declaration = Grammar.Entry.create gram "declaration"
let type_decl = Grammar.Entry.create gram "type_decl"
let body_decl = Grammar.Entry.create gram "body_decl"

let rec make_arrows = function 
  | [c] -> c
  | c::cl -> mkArrow c (make_arrows cl)

(* This is a quick packing of long idents into anything *)
(* They are supposed to be unpacked and correctly scoped later *)
let path_of_string s = make_ln top_path (label_of_string s) 
let ln_of_longident lid = 
  make_ln top_path (label_of_string (String.concat "." lid))
let mp_of_longident lid = 
  MPdot(top_path, (label_of_string (String.concat "." lid)))
(*let id_of_longident lid =
  id_of_string (String.concat "." lid)*)

let fold_functor_type args mty = 
  List.fold_right 
    (fun (id,arg_t) mty -> MTEfunsig (id,arg_t,mty))
    args mty

let fold_functor_expr args me = 
  List.fold_right 
    (fun (id,arg_t) me -> MEfunctor (id,arg_t,me))
    args me

let make_entry d = 
  let one_inductive npar par (l,typ,cl) =
    { mind_entry_nparams = npar;
      mind_entry_params = par;
      mind_entry_typename = l;
      mind_entry_arity = typ;
      mind_entry_consnames = List.map fst cl;
      mind_entry_lc = List.map snd cl } 
  in
    match d with
      | Value (l,typ_o,body_o) -> 
	  l, 
	  SPEconst { const_entry_body = body_o;
		     const_entry_type = typ_o }
      | Inductive (par, ((l,_,_)::_ as inds)) ->
	  let npar = List.length par in
	  let par' = 
	    List.rev (List.map (fun (id,c) -> (id, LocalAssum c)) par) 
	  in
	  let inds' = List.map (one_inductive npar par') inds in
	    l,
	    SPEmind { mind_entry_finite = true; 
		      mind_entry_inds = inds' }
      | ModuleType (l, mte) ->
	  l, SPEmodtype mte
      | Module (l,args,mty_o,body_o) ->
	  l, 
	  SPEmodule 
	    { mod_entry_type = 
		option_app (fold_functor_type args) mty_o;
	      mod_entry_expr = 
		option_app (fold_functor_expr args) body_o }

let make_sig decls = 
  let msid = msid_of_string "sig" in
  let entries = List.map make_entry decls in
    MTEsig (msid, entries)

let make_struct decls = 
  let msid = msid_of_string "struct" in
  let entries = List.map make_entry decls in
    MEstruct (msid, entries)

EXTEND
  longident:
  [ [ id = IDENT; lid = LIST0 FIELD -> id::lid ] ];
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
    | "Rel"; n = INT ->
	mkRel (int_of_string n)
    | "Set" ->
	mkSet
    | "Prop" ->
	mkProp
    | "Type" ->
	mkType (new_univ())
    | "Const"; lid = longident ->
	mkConst (ln_of_longident lid, [||])
    | "Ind"; lid = longident; n = INT ->
	let n = int_of_string n in
	mkMutInd ((ln_of_longident lid, n), [||])
    | "Construct"; lid = longident; n = INT; i = INT ->
	let n = int_of_string n and i = int_of_string i in
	mkMutConstruct (((ln_of_longident lid, n), i), [||])
    | "["; na = name; ":"; t = term; "]"; c = term ->
	mkLambda (na,t,c)
    | "("; "_"; ":"; t = term; ")"; c = term ->
	mkProd (Anonymous,t,c)
    | "("; id = IDENT; ":"; t = term; ")"; c = term ->
	mkProd (Name (id_of_string id),t,c)
    | "("; id = IDENT; "->"; cl = LIST1 term SEP "->"; ")" ->
	mkArrow (mkVar (id_of_string id)) (make_arrows cl)
    | c = term; "->"; cl = LIST1 term SEP "->" ->
	mkArrow c (make_arrows cl)
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
    | "<"; p = term; ">";        (* n = number of parameters of id *)
	"Case"; c = term; ":"; "["; n=INT; "]"; "Ind"; id = IDENT; i = INT;
	"of"; bl = LIST0 term; "end" ->
	  let ind = (path_of_string id,int_of_string i) in
	  let nc = List.length bl in
	  let dummy_pats = Array.create nc RegularPat in
	  let dummy_ci = int_of_string n,(ind,[||],nc,None,dummy_pats) in
	  mkMutCase (dummy_ci, p, c, Array.of_list bl)
    | "Fix"; id = IDENT; "/"; i = INT; ":"; ty = term; 
       ":="; body = term ->
	 mkFix (([|int_of_string i|],0),
		([|Name (id_of_string id)|], [|ty|], [|body|])) 
  ] ];

  type_decl:
  [ [ ":"; t = term -> t ] ];

  body_decl:
  [ [ ":="; c = term -> c ] ];

  declaration:
  [ [ "Definition"; id = IDENT; typ_o = OPT type_decl; 
      body_o = OPT body_decl ->
        Value (label_of_string id, typ_o, body_o)
    | 
      "Inductive"; "["; params = LIST0 nametype SEP ";"; "]"; 
      inds = LIST1 inductive SEP "with" ->
	Inductive (params,inds)
    | 
      "Module"; id = IDENT; args = LIST0 module_arg; 
      mt_o = OPT module_type_decl; body_o = OPT module_body_decl ->
	Module (label_of_string id, args, mt_o, body_o)
    |
      "Module"; "Type"; id = IDENT; ":="; mty = module_type ->
	ModuleType (label_of_string id, mty)
    ] ];

  module_arg:
  [ [ "("; id = IDENT; ":"; mt = module_type; ")" ->
	(mbid_of_string id, mt) ] ];

  module_type:
  [ [ "sig"; dl = LIST0 declaration; "end" -> 
	make_sig dl 
    | "funsig"; "("; id = IDENT; ":";  arg_t = module_type; ")"; 
      body_t = module_type ->
	MTEfunsig (mbid_of_string id, arg_t, body_t)
    | lid = longident ->
	MTEident (ln_of_longident lid)
    ] ];

  module_type_decl:
  [ [ ":"; mt = module_type -> mt ] ];

  module_expr:
  [ [ "struct"; dl = LIST0 declaration; "end" ->
	make_struct dl
    | "functor"; "("; id = IDENT; ":";  arg_t = module_type; ")"; 
      body_e = module_expr ->
	MEfunctor (mbid_of_string id, arg_t, body_e)
    | m1 = module_expr; m2 = module_expr ->
	MEapply (m1,m2)
    | lid = longident ->
	MEident (mp_of_longident lid)
    | "("; m = module_expr; ")" -> 
	m
    ] ];

  module_body_decl:
  [ [ ":="; me = module_expr -> me ] ];


  command: 
  [ [ 
      d = declaration; "." ->
	(match d with 
	   | Module(l,args,mt_o,None) ->
	       BeginModule (l,args,mt_o)
	   | _ -> Entry (make_entry d)
	)
    | "End"; id = IDENT; "." ->
	EndModule (label_of_string id)
    | "Abbrev"; id = IDENT; ":="; c=term; "." ->
	Abbrev (id_of_string id, c) 
    | "Check"; c = term; "." ->
	Check c
    | "Print"; lid = longident; "." ->
	Print (ln_of_longident lid)
    | "Reduce"; c = term; "." ->
        Reduce c
    | EOI -> raise End_of_file
  ] ];

  inductive: 
  [ [ id = IDENT; ":"; ar = term; ":="; constrs = LIST0 constructor SEP "|" ->
        (label_of_string id,ar,constrs)
  ] ];
  constructor:
  [ [ id = IDENT; ":"; c = term -> (label_of_string id,c) ] ];
END

(* Pretty-print. *)

let print_univers = ref false
let print_casts = ref false

let print_type u =
  if !print_univers then [< 'sTR "Type"; pr_uni u >]
  else [< 'sTR "Type" >]

let print_name = function
  | Anonymous -> [< 'sTR "_" >]
  | Name id -> pr_id id

let print_rel bv n = 
  try 
    print_name (List.nth bv (pred n)) 
  with
    | Failure _ -> [< 'sTR "Rel"; 'sPC; 'iNT n >]

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
  | IsSort (Prop Pos) -> [< 'sTR "Set" >]
  | IsSort (Prop Null) -> [< 'sTR "Prop" >]
  | IsSort (Type u) -> print_type u
  | IsLambda (na, t, c) ->
      [< 'sTR"["; print_name na; 'sTR":"; pp bv t; 'sTR"]"; pp (na::bv) c >]
  | IsProd (Anonymous, t, c) ->
      let brack = match kind_of_term t with
	| IsProd _ -> true
	| _ -> false
      in
	if brack then
	  [< 'sTR "("; pp bv t; 'sTR ")"; 
	     'sTR"->"; pp (Anonymous::bv) c >]
	else
	  [< pp bv t; 'sTR"->"; pp (Anonymous::bv) c >]
  | IsProd (na, t, c) ->
      [< 'sTR"("; print_name na; 'sTR":"; pp bv t; 'sTR")"; pp (na::bv) c >]
  | IsCast (c, t) ->
      if !print_casts then 
	[< 'sTR"("; pp bv c; 'sTR"::"; pp bv t; 'sTR")" >]
      else 
	pp bv c
  | IsApp(h, v) ->
      [< 'sTR"("; pp bv h; 'sPC;
         prvect_with_sep (fun () -> [< 'sPC >]) (pp bv) v; 'sTR")" >]
  | IsConst (ln, _) ->
      [< 'sTR"Const "; pr_ln ln >]
  | IsMutInd ((ln,i), _) ->
      [< 'sTR"Ind "; pr_ln ln; 'sTR" "; 'iNT i >]
  | IsMutConstruct (((ln,i),j), _) ->
      [< 'sTR"Construct "; pr_ln ln; 'sTR" "; 'iNT i; 
	 'sTR" "; 'iNT j >]
  | IsVar id -> [< 'sTR "'"; pr_id id; 'sTR "'" >]
  | IsRel n -> print_rel bv n
  | IsFix (([|i|],_),([|Name id|],[|t|],[|c|])) ->
      [< 'sTR"Fix ";pr_id id;'sTR"/";'iNT i;'sTR":"; pp bv t; 
	 'sTR":="; pp ((Name id)::bv) c >]
  | IsMutCase (ci,p,c,bl) ->
      [< 'sTR"<";pp bv p; 'sTR">";'sTR"Case "; pp bv c; 'sTR" of "; 
	 prvect_with_sep pr_spc (pp bv) bl; 'sTR" end" >]
  | _ -> [< 'sTR"<???>" >]

let pr_term ctx = pp (fold_rel_context (fun _ (n,_,_) l -> n::l) ctx [])

