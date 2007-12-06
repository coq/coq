(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Flags
open Util
open Names
open Nameops
open Vernacentries
open Reduction
open Term
open Libnames
open Topconstr

open Prename
open Pmisc
open Putil
open Ptype
open Past
open Penv
open Pmonad
open Vernacexpr


(* We define new entries for programs, with the use of this module
 * Programs. These entries are named Programs.<foo>
 *)

module Gram = Pcoq.Gram
module Constr = Pcoq.Constr
module Tactic = Pcoq.Tactic

module Programs =
  struct
    let gec s = Gram.Entry.create ("Programs."^s)
    (* types *)
    let type_v   = gec "type_v"
    let type_v0  = gec "type_v0"
    let type_v1  = gec "type_v1"
    let type_v2  = gec "type_v2"
    let type_v3  = gec "type_v3"
    let type_v_app  = gec "type_v_app"
    let type_c   = gec "type_c"
    let effects  = gec "effects"
    let reads    = gec "reads"
    let writes   = gec "writes"
    let pre_condition = gec "pre_condition"
    let post_condition = gec "post_condition"
    (* binders *)
    let binder  = gec "binder"
    let binder_type = gec "binder_type"
    let binders  = gec "binders"
    (* programs *)
    let program = gec "program"
    let prog1 = gec "prog1"
    let prog2 = gec "prog2"
    let prog3 = gec "prog3"
    let prog4 = gec "prog4"
    let prog5 = gec "prog5"
    let prog6 = gec "prog6"
    let prog7 = gec "prog7"
    let ast1 = gec "ast1"
    let ast2 = gec "ast2"
    let ast3 = gec "ast3"
    let ast4 = gec "ast4"
    let ast5 = gec "ast5"
    let ast6 = gec "ast6"
    let ast7 = gec "ast7"
    let arg = gec "arg"
    let block = gec "block"
    let block_statement = gec "block_statement"
    let relation = gec "relation"
    let variable = gec "variable"
    let invariant = gec "invariant"
    let variant = gec "variant"
    let assertion = gec "assertion"
    let precondition = gec "precondition"
    let postcondition = gec "postcondition"
    let predicate = gec "predicate"
    let name = gec "name"
  end

open Programs

let ast_of_int n = 
  CDelimiters
    (dummy_loc, "Z", CNumeral (dummy_loc, Bignat.POS (Bignat.of_string n)))

let constr_of_int n =
  Constrintern.interp_constr Evd.empty (Global.env ()) (ast_of_int n)

open Util
open Coqast

let mk_id loc id = mkRefC (Ident (loc, id))
let mk_ref loc s = mk_id loc (Constrextern.id_of_v7_string s)
let mk_appl loc1 loc2 f args =
  CApp (join_loc loc1 loc2, (None,mk_ref loc1 f), List.map (fun a -> a,None) args)

let conj_assert {a_name=n;a_value=a} {a_value=b} = 
  let loc1 = constr_loc a in
  let loc2 = constr_loc a in
  { a_value = mk_appl loc1 loc2 "and" [a;b]; a_name = n }

let conj = function
    None,None     -> None
  | None,b        -> b
  | a,None        -> a
  | Some a,Some b -> Some (conj_assert a b)

let without_effect loc d = 
  { desc = d; pre = []; post = None; loc = loc; info = () }

let isevar = Expression isevar

let bin_op op loc e1 e2 =
  without_effect loc
    (Apply (without_effect loc (Expression (constant op)),
            [ Term e1; Term e2 ]))

let un_op op loc e =
  without_effect loc
    (Apply (without_effect loc (Expression (constant op)), [Term e]))

let bool_bin op loc a1 a2 =
  let w = without_effect loc in
  let d = SApp ( [Variable op], [a1; a2]) in
  w d

let bool_or  loc = bool_bin connective_or loc
let bool_and loc = bool_bin connective_and loc

let bool_not loc a =
  let w = without_effect loc in
  let d = SApp ( [Variable connective_not ], [a]) in
  w d

let ast_zwf_zero loc = mk_appl loc loc "Zwf" [mk_ref loc "Z0"]

(* program -> Coq AST *)

let bdize c =
  let env = 
    Global.env_of_context (Pcicenv.cci_sign_of Prename.empty_ren Penv.empty)
  in
  Constrextern.extern_constr true env c

let rec coqast_of_program loc = function
  | Variable id -> mk_id loc id
  | Acc id -> mk_id loc id
  | Apply (f,l) -> 
      let f = coqast_of_program f.loc f.desc in
      let args = List.map 
		   (function Term t -> (coqast_of_program t.loc t.desc,None)
		      | _ -> invalid_arg "coqast_of_program") l
      in
      CApp (dummy_loc, (None,f), args)
  | Expression c -> bdize c
  | _ -> invalid_arg "coqast_of_program"

(* The construction `for' is syntactic sugar.
 *
 * for i = v1 to v2 do { invariant Inv } block done
 *
 * ==> (let rec f i { variant v2+1-i } = 
 *        { i <= v2+1 /\ Inv(i) }
 *        (if i > v2 then tt else begin block; (f (i+1)) end) 
 *        { Inv(v2+1) }
 *      in (f v1)) { Inv(v2+1) }
 *)

let ast_plus_un loc ast =
  let un = ast_of_int "1" in
  mk_appl loc loc "Zplus" [ast;un]

let make_ast_for loc i v1 v2 inv block =
  let f = for_name() in
  let id_i = id_of_string i in
  let var_i = without_effect loc (Variable id_i) in
  let var_f = without_effect loc (Variable f) in
  let succ_v2 = 
    let a_v2 = coqast_of_program v2.loc v2.desc in
    ast_plus_un loc a_v2 in
  let post = named_app (subst_ast_in_ast [ id_i, succ_v2 ]) inv in
  let e1 =
    let test = bin_op "Z_gt_le_bool" loc var_i v2 in
    let br_t = without_effect loc (Expression (constant "tt")) in
    let br_f = 
      let un = without_effect loc (Expression (constr_of_int "1")) in
      let succ_i = bin_op "Zplus" loc var_i un in
      let f_succ_i = without_effect loc (Apply (var_f, [Term succ_i])) in
      without_effect loc (Seq (block @ [Statement f_succ_i]))
    in
    let inv' = 
      let i_le_sv2 = mk_appl loc loc "Zle" [mk_ref loc i; succ_v2] in
      conj_assert {a_value=i_le_sv2;a_name=inv.a_name} inv
    in
    { desc = If(test,br_t,br_f); loc = loc; 
      pre = [pre_of_assert false inv']; post = Some post; info = () } 
  in
  let bl = 
    let typez = mk_ref loc "Z" in
    [(id_of_string i, BindType (TypePure typez))] 
  in
  let fv1 = without_effect loc (Apply (var_f, [Term v1])) in
  let v = TypePure (mk_ref loc "unit") in
  let var = 
    let a = mk_appl loc loc "Zminus" [succ_v2;mk_ref loc i] in
    (a, ast_zwf_zero loc)
  in
  Let (f, without_effect loc (LetRec (f,bl,v,var,e1)), fv1)

let mk_prog loc p pre post =
  { desc = p.desc; 
    pre = p.pre @ pre; 
    post = conj (p.post,post); 
    loc = loc; 
    info = () }

if !Flags.v7 then
GEXTEND Gram

  (* Types ******************************************************************)
  type_v:
    [ [ t = type_v0 -> t ] ]
  ;
  type_v0:
    [ [ t = type_v1 -> t ] ]
  ;
  type_v1:
    [ [ t = type_v2 -> t ] ]
  ;
  type_v2:
    [ LEFTA
      [ v = type_v2; IDENT "ref" -> Ref v
      | t = type_v3 -> t ] ]
  ;
  type_v3:
    [ [ IDENT "array"; size = Constr.constr; "of"; v = type_v0 ->
          Array (size,v)
      | IDENT "fun"; bl = binders; c = type_c -> make_arrow bl c
      | c = Constr.constr -> TypePure c	  
      ] ]
  ;
  type_c:
    [ [ IDENT "returns"; id = IDENT; ":"; v = type_v;
        e = effects; p = OPT pre_condition; q = OPT post_condition; "end" ->
        ((id_of_string id, v), e, list_of_some p, q)
      ] ] 
  ;
  effects:
    [ [ r = OPT reads; w = OPT writes ->
	let r' = match r with Some l -> l | _ -> [] in
	let w' = match w with Some l -> l | _ -> [] in
	List.fold_left (fun e x -> Peffect.add_write x e)
	  (List.fold_left (fun e x -> Peffect.add_read x e) Peffect.bottom r')
          w'
      ] ]
  ;
  reads:
    [ [ IDENT "reads"; l = LIST0 IDENT SEP "," -> List.map id_of_string l ] ]
  ;
  writes:
    [ [ IDENT "writes"; l=LIST0 IDENT SEP "," -> List.map id_of_string l ] ]
  ;
  pre_condition:
    [ [ IDENT "pre"; c = predicate -> pre_of_assert false c ] ]
  ;
  post_condition:
    [ [ IDENT "post"; c = predicate -> c ] ]
  ;

  (* Binders (for both types and programs) **********************************)
  binder:
    [ [ "("; sl = LIST1 IDENT SEP ","; ":"; t = binder_type ; ")" ->
	  List.map (fun s -> (id_of_string s, t)) sl
      ] ]
  ;
  binder_type:
    [ [ "Set" -> BindSet
      | v = type_v -> BindType v
      ] ]
  ;
  binders:
    [ [ bl = LIST0 binder -> List.flatten bl ] ] 
  ;

  (* annotations *)
  predicate:
    [ [ c = Constr.constr; n = name -> { a_name = n; a_value = c } ] ]
  ;
  name:
    [ [ "as"; s = IDENT -> Name (id_of_string s)
      | -> Anonymous
      ] ]
  ;

  (* Programs ***************************************************************)
  variable:
    [ [ s = IDENT -> id_of_string s ] ]
  ;
  assertion:
    [ [ "{"; c = predicate; "}" -> c ] ]
  ;
  precondition:
    [ [ "{"; c = predicate; "}" -> pre_of_assert false c ] ]
  ;
  postcondition:
    [ [ "{"; c = predicate; "}" -> c ] ]
  ;
  program:
    [ [ p = prog1 -> p ] ]
  ;
  prog1:
    [ [ pre = LIST0 precondition; ast = ast1; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog2:
    [ [ pre = LIST0 precondition; ast = ast2; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog3:
    [ [ pre = LIST0 precondition; ast = ast3; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog4:
    [ [ pre = LIST0 precondition; ast = ast4; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog5:
    [ [ pre = LIST0 precondition; ast = ast5; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog6:
    [ [ pre = LIST0 precondition; ast = ast6; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;

  ast1:
    [ [ x = prog2; IDENT "or"; y = prog1  -> bool_or loc x y
      | x = prog2; IDENT "and"; y = prog1 -> bool_and loc x y
      | x = prog2 -> x
      ] ]
  ;
  ast2:
    [ [ IDENT "not"; x = prog3 -> bool_not loc x
      | x = prog3 -> x
      ] ]
  ;
  ast3:
    [ [ x = prog4; rel = relation; y = prog4 -> bin_op rel loc x y
      | x = prog4 -> x
      ] ]
    ;
  ast4:
    [ [ x = prog5; "+"; y = prog4 -> bin_op "Zplus" loc x y
      | x = prog5; "-"; y = prog4 -> bin_op "Zminus" loc x y
      | x = prog5 -> x
      ] ]
    ;
  ast5:
    [ [ x = prog6; "*"; y = prog5 -> bin_op "Zmult" loc x y 
      | x = prog6 -> x
      ] ]
    ;
  ast6:
    [ [ "-"; x = prog6 -> un_op "Zopp" loc x
      | x = ast7 -> without_effect loc x
      ] ]
    ;
  ast7:
    [ [ v = variable -> 
	  Variable v
      | n = INT ->
	  Expression (constr_of_int n)
      | "!"; v = variable ->
	  Acc v
      | "?" ->
	  isevar
      | v = variable; ":="; p = program ->
	  Aff (v,p)
      | v = variable; "["; e = program; "]" -> TabAcc (true,v,e)
      | v = variable; "#"; "["; e = program; "]" -> TabAcc (true,v,e)
      | v = variable; "["; e = program; "]"; ":="; p = program -> 
	  TabAff (true,v,e,p)
      | v = variable; "#"; "["; e = program; "]"; ":="; p = program -> 
	  TabAff (true,v,e,p)
      | IDENT "if"; e1 = program; IDENT "then"; e2 = program;
	IDENT "else"; e3 = program ->
	  If (e1,e2,e3)
      | IDENT "if"; e1 = program; IDENT "then"; e2 = program ->
	  If (e1,e2,without_effect loc (Expression (constant "tt")))
      | IDENT "while"; b = program; IDENT "do"; 
	"{"; inv = OPT invariant; IDENT "variant"; wf = variant; "}";
	bl = block; IDENT "done" ->
	  While (b, inv, wf, bl)
      | IDENT "for"; i = IDENT; "="; v1 = program; IDENT "to"; v2 = program;
	IDENT "do"; "{"; inv = invariant; "}"; 
	bl = block; IDENT "done" -> 
	  make_ast_for loc i v1 v2 inv bl
      | IDENT "let"; v = variable; "="; IDENT "ref"; p1 = program;
	"in"; p2 = program ->
	  LetRef (v, p1, p2)
      | IDENT "let"; v = variable; "="; p1 = program; "in"; p2 = program ->
	  Let (v, p1, p2)
      | IDENT "begin"; b = block; "end" ->
	  Seq b
      | IDENT "fun"; bl = binders; "->"; p = program ->
	  Lam (bl,p)
      | IDENT "let"; IDENT "rec"; f = variable; 
	bl = binders; ":"; v = type_v;
	"{"; IDENT "variant"; var = variant; "}"; "="; p = program ->
	  LetRec (f,bl,v,var,p)
      | IDENT "let"; IDENT "rec"; f = variable; 
	bl = binders; ":"; v = type_v;
	"{"; IDENT "variant"; var = variant; "}"; "="; p = program;
 	"in"; p2 = program ->
	  Let (f, without_effect loc (LetRec (f,bl,v,var,p)), p2)

      | "@"; s = STRING; p = program ->
	  Debug (s,p)

      | "("; p = program; args = LIST0 arg; ")" ->
	  match args with 
	      [] -> 
		if p.pre<>[] or p.post<>None then
		  Pp.warning "Some annotations are lost";
		p.desc
            | _  -> 
		Apply(p,args)
     ] ]
  ;
  arg:
    [ [ "'"; t = type_v -> Type t
      | p = program -> Term p
      ] ]
  ;
  block:
    [ [ s = block_statement; ";"; b = block -> s::b
      | s = block_statement                 -> [s] ] ]
  ;
  block_statement:
    [ [ IDENT "label"; s = IDENT -> Label s
      | IDENT "assert"; c = assertion -> Assert c 
      | p = program -> Statement p ] ]
  ;
  relation:
    [ [ "<"  -> "Z_lt_ge_bool"
      | "<=" -> "Z_le_gt_bool"
      | ">"  -> "Z_gt_le_bool"
      | ">=" -> "Z_ge_lt_bool"
      | "="  -> "Z_eq_bool"
      | "<>" -> "Z_noteq_bool" ] ] 
  ;

  (* Other entries (invariants, etc.) ***************************************)
  invariant:
    [ [ IDENT "invariant"; c = predicate -> c ] ]
  ;
  variant:
    [ [ c = Constr.constr; IDENT "for"; r = Constr.constr -> (c, r)
      | c = Constr.constr -> (c, ast_zwf_zero loc) ] ]
  ;
  END
else
GEXTEND Gram
  GLOBAL: type_v program;

  (* Types ******************************************************************)
  type_v:
    [ [ t = type_v0 -> t ] ]
  ;
  type_v0:
    [ [ t = type_v1 -> t ] ]
  ;
  type_v1:
    [ [ t = type_v2 -> t ] ]
  ;
  type_v2:
    [ LEFTA
      [ v = type_v2; IDENT "ref" -> Ref v
      | t = type_v3 -> t ] ]
  ;
  type_v3:
    [ [ IDENT "array"; size = Constr.constr; IDENT "of"; v = type_v0 ->
          Array (size,v)
      | "fun"; bl = binders; c = type_c -> make_arrow bl c
      | c = Constr.constr -> TypePure c	  
      ] ]
  ;
  type_c:
    [ [ IDENT "returns"; id = IDENT; ":"; v = type_v;
        e = effects; p = OPT pre_condition; q = OPT post_condition; "end" ->
        ((id_of_string id, v), e, list_of_some p, q)
      ] ] 
  ;
  effects:
    [ [ r = OPT reads; w = OPT writes ->
	let r' = match r with Some l -> l | _ -> [] in
	let w' = match w with Some l -> l | _ -> [] in
	List.fold_left (fun e x -> Peffect.add_write x e)
	  (List.fold_left (fun e x -> Peffect.add_read x e) Peffect.bottom r')
          w'
      ] ]
  ;
  reads:
    [ [ IDENT "reads"; l = LIST0 IDENT SEP "," -> List.map id_of_string l ] ]
  ;
  writes:
    [ [ IDENT "writes"; l=LIST0 IDENT SEP "," -> List.map id_of_string l ] ]
  ;
  pre_condition:
    [ [ IDENT "pre"; c = predicate -> pre_of_assert false c ] ]
  ;
  post_condition:
    [ [ IDENT "post"; c = predicate -> c ] ]
  ;

  (* Binders (for both types and programs) **********************************)
  binder:
    [ [ "("; sl = LIST1 IDENT SEP ","; ":"; t = binder_type ; ")" ->
	  List.map (fun s -> (id_of_string s, t)) sl
      ] ]
  ;
  binder_type:
    [ [ "Set" -> BindSet
      | v = type_v -> BindType v
      ] ]
  ;
  binders:
    [ [ bl = LIST0 binder -> List.flatten bl ] ] 
  ;

  (* annotations *)
  predicate:
    [ [ c = Constr.constr; n = name -> { a_name = n; a_value = c } ] ]
  ;
  dpredicate:
    [ [ c = Constr.lconstr; n = name -> { a_name = n; a_value = c } ] ]
  ;
  name:
    [ [ "as"; s = IDENT -> Name (id_of_string s)
      | -> Anonymous
      ] ]
  ;

  (* Programs ***************************************************************)
  variable:
    [ [ s = IDENT -> id_of_string s ] ]
  ;
  assertion:
    [ [ "{"; c = dpredicate; "}" -> c ] ]
  ;
  precondition:
    [ [ "{"; c = dpredicate; "}" -> pre_of_assert false c ] ]
  ;
  postcondition:
    [ [ "{"; c = dpredicate; "}" -> c ] ]
  ;
  program:
    [ [ p = prog1 -> p ] ]
  ;
  prog1:
    [ [ pre = LIST0 precondition; ast = ast1; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog2:
    [ [ pre = LIST0 precondition; ast = ast2; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog3:
    [ [ pre = LIST0 precondition; ast = ast3; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog4:
    [ [ pre = LIST0 precondition; ast = ast4; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog5:
    [ [ pre = LIST0 precondition; ast = ast5; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;
  prog6:
    [ [ pre = LIST0 precondition; ast = ast6; post = OPT postcondition ->
	  mk_prog loc ast pre post ] ]
  ;

  ast1:
    [ [ x = prog2; IDENT "or"; y = prog1  -> bool_or loc x y
      | x = prog2; IDENT "and"; y = prog1 -> bool_and loc x y
      | x = prog2 -> x
      ] ]
  ;
  ast2:
    [ [ IDENT "not"; x = prog3 -> bool_not loc x
      | x = prog3 -> x
      ] ]
  ;
  ast3:
    [ [ x = prog4; rel = relation; y = prog4 -> bin_op rel loc x y
      | x = prog4 -> x
      ] ]
    ;
  ast4:
    [ [ x = prog5; "+"; y = prog4 -> bin_op "Zplus" loc x y
      | x = prog5; "-"; y = prog4 -> bin_op "Zminus" loc x y
      | x = prog5 -> x
      ] ]
    ;
  ast5:
    [ [ x = prog6; "*"; y = prog5 -> bin_op "Zmult" loc x y 
      | x = prog6 -> x
      ] ]
    ;
  ast6:
    [ [ "-"; x = prog6 -> un_op "Zopp" loc x
      | x = ast7 -> without_effect loc x
      ] ]
    ;
  ast7:
    [ [ v = variable -> 
	  Variable v
      | n = INT ->
	  Expression (constr_of_int n)
      | "!"; v = variable ->
	  Acc v
      | "?" ->
	  isevar
      | v = variable; ":="; p = program ->
	  Aff (v,p)
      | v = variable; "["; e = program; "]" -> TabAcc (true,v,e)
      | v = variable; "#"; "["; e = program; "]" -> TabAcc (true,v,e)
      | v = variable; "["; e = program; "]"; ":="; p = program -> 
	  TabAff (true,v,e,p)
      | v = variable; "#"; "["; e = program; "]"; ":="; p = program -> 
	  TabAff (true,v,e,p)
      | "if"; e1 = program; "then"; e2 = program; "else"; e3 = program ->
	  If (e1,e2,e3)
      | "if"; e1 = program; "then"; e2 = program ->
	  If (e1,e2,without_effect loc (Expression (constant "tt")))
      | IDENT "while"; b = program; IDENT "do"; 
	"{"; inv = OPT invariant; IDENT "variant"; wf = variant; "}";
	bl = block; IDENT "done" ->
	  While (b, inv, wf, bl)
      | "for"; i = IDENT; "="; v1 = program; IDENT "to"; v2 = program;
	IDENT "do"; "{"; inv = invariant; "}"; 
	bl = block; IDENT "done" -> 
	  make_ast_for loc i v1 v2 inv bl
      | "let"; v = variable; "="; IDENT "ref"; p1 = program;
	"in"; p2 = program ->
	  LetRef (v, p1, p2)
      | "let"; v = variable; "="; p1 = program; "in"; p2 = program ->
	  Let (v, p1, p2)
      | IDENT "begin"; b = block; "end" ->
	  Seq b
      | "fun"; bl = binders; "=>"; p = program ->
	  Lam (bl,p)
      | "let"; IDENT "rec"; f = variable; 
	bl = binders; ":"; v = type_v;
	"{"; IDENT "variant"; var = variant; "}"; "="; p = program ->
	  LetRec (f,bl,v,var,p)
      | "let"; IDENT "rec"; f = variable; 
	bl = binders; ":"; v = type_v;
	"{"; IDENT "variant"; var = variant; "}"; "="; p = program;
 	"in"; p2 = program ->
	  Let (f, without_effect loc (LetRec (f,bl,v,var,p)), p2)

      | "@"; s = STRING; p = program ->
	  Debug (s,p)

      | "("; p = program; args = LIST0 arg; ")" ->
	  match args with 
	      [] -> 
		if p.pre<>[] or p.post<>None then
		  Pp.warning "Some annotations are lost";
		p.desc
            | _  -> 
		Apply(p,args)
     ] ]
  ;
  arg:
    [ [ "'"; t = type_v -> Type t
      | p = program -> Term p
      ] ]
  ;
  block:
    [ [ s = block_statement; ";"; b = block -> s::b
      | s = block_statement                 -> [s] ] ]
  ;
  block_statement:
    [ [ IDENT "label"; s = IDENT -> Label s
      | IDENT "assert"; c = assertion -> Assert c 
      | p = program -> Statement p ] ]
  ;
  relation:
    [ [ "<"  -> "Z_lt_ge_bool"
      | "<=" -> "Z_le_gt_bool"
      | ">"  -> "Z_gt_le_bool"
      | ">=" -> "Z_ge_lt_bool"
      | "="  -> "Z_eq_bool"
      | "<>" -> "Z_noteq_bool" ] ] 
  ;

  (* Other entries (invariants, etc.) ***************************************)
  invariant:
    [ [ IDENT "invariant"; c = predicate -> c ] ]
  ;
  variant:
    [ [ c = Constr.constr; "for"; r = Constr.constr -> (c, r)
      | c = Constr.constr -> (c, ast_zwf_zero loc) ] ]
  ;
  END
;;

let wit_program, globwit_program, rawwit_program =
  Genarg.create_arg "program"
let wit_type_v, globwit_type_v, rawwit_type_v =
  Genarg.create_arg "type_v"

open Pp
open Util
open Himsg
open Vernacinterp
open Vernacexpr
open Declare

let is_assumed global ids =
  if List.length ids = 1 then
    msgnl (str (if global then "A global variable " else "") ++ 
	     pr_id (List.hd ids) ++ str " is assumed")
  else
    msgnl (str (if global then "Some global variables " else "") ++
	     prlist_with_sep (fun () -> (str ", ")) pr_id ids ++
	     str " are assumed")

open Pcoq

(* Variables *)

let wit_variables, globwit_variables, rawwit_variables =
  Genarg.create_arg "variables"

let variables = Gram.Entry.create "Variables"

GEXTEND Gram
  variables: [ [ l = LIST1 Prim.ident SEP "," -> l ] ];
END

let pr_variables _prc _prtac l = spc() ++ prlist_with_sep pr_coma pr_id l

let _ =
  Pptactic.declare_extra_genarg_pprule true
    (rawwit_variables, pr_variables)
    (globwit_variables, pr_variables)
    (wit_variables, pr_variables)

(* then_tac *)

open Genarg
open Tacinterp

let pr_then_tac _ prt = function
  | None -> mt ()
  | Some t -> pr_semicolon () ++ prt t

ARGUMENT EXTEND then_tac
  TYPED AS tactic_opt 
  PRINTED BY pr_then_tac
  INTERPRETED BY interp_genarg
  GLOBALIZED BY intern_genarg
| [ ";" tactic(t) ] -> [ Some t ]
| [ ] -> [ None ]
END

(* Correctness *)

VERNAC COMMAND EXTEND Correctness
  [ "Correctness" preident(str) program(pgm) then_tac(tac) ]
   -> [ Ptactic.correctness str pgm (Option.map Tacinterp.interp tac) ]
END

(* Show Programs *)

let show_programs () =
  fold_all 
    (fun (id,v) _ -> 
      msgnl (pr_id id ++ str " : " ++ 
      hov 2 (match v with TypeV v -> pp_type_v v
	| Set -> (str "Set")) ++
      fnl ()))
    Penv.empty ()

VERNAC COMMAND EXTEND ShowPrograms
  [ "Show" "Programs" ] -> [ show_programs () ]
END

(* Global Variable *)

let global_variable ids v =
  List.iter
    (fun id -> if Penv.is_global id then
      Util.errorlabstrm "PROGVARIABLE"
	(str"Clash with previous constant " ++ pr_id id))
    ids;
  Pdb.check_type_v (all_refs ()) v;
  let env = empty in
  let ren = update empty_ren "" [] in
  let v = Ptyping.cic_type_v env ren v in
  if not (is_mutable v) then begin
    let c = 
      Entries.ParameterEntry (trad_ml_type_v ren env v),
      Decl_kinds.IsAssumption Decl_kinds.Definitional in
    List.iter 
      (fun id -> ignore (Declare.declare_constant id c)) ids;
    if_verbose (is_assumed false) ids
  end;
  if not (is_pure v) then begin
    List.iter (fun id -> ignore (Penv.add_global id v None)) ids;
    if_verbose (is_assumed true) ids
  end

VERNAC COMMAND EXTEND ProgVariable
  [ "Global" "Variable" variables(ids) ":" type_v(t) ]
  -> [ global_variable ids t]
END

let pr_id id = pr_id (Constrextern.v7_to_v8_id id)

(* Type printer *)

let pr_reads = function
  | [] -> mt ()
  | l -> spc () ++
      hov 0 (str "reads" ++ spc () ++ prlist_with_sep pr_coma pr_id l)

let pr_writes = function
  | [] -> mt ()
  | l -> spc () ++
      hov 0 (str "writes" ++ spc () ++ prlist_with_sep pr_coma pr_id l)

let pr_effects x =
  let (ro,rw) = Peffect.get_repr x in pr_reads ro ++ pr_writes rw

let pr_predicate delimited { a_name = n; a_value = c } =
  (if delimited then Ppconstr.pr_lconstr else Ppconstr.pr_constr) c ++
  (match n with Name id -> spc () ++ str "as " ++ pr_id id | Anonymous -> mt())

let pr_assert b { p_name = x; p_value = v } =
  pr_predicate b { a_name = x; a_value = v }

let pr_pre_condition_list = function
  | [] -> mt ()
  | [pre] -> spc() ++ hov 0 (str "pre" ++ spc () ++ pr_assert false pre)
  | _ -> assert false

let pr_post_condition_opt = function
  | None -> mt ()
  | Some post ->
      spc() ++ hov 0 (str "post" ++ spc () ++ pr_predicate false post)

let rec pr_type_v_v8 = function
  | Array (a,v) ->
      str "array" ++ spc() ++ Ppconstr.pr_constr a ++ spc() ++ str "of " ++
      pr_type_v_v8 v
  | v -> pr_type_v3 v

and pr_type_v3 = function
  | Ref v -> pr_type_v3 v ++ spc () ++ str "ref"
  | Arrow (bl,((id,v),e,prel,postl)) ->
      str "fun" ++ spc() ++ hov 0 (prlist_with_sep cut pr_binder bl) ++
      spc () ++ str "returns" ++ spc () ++ pr_id id ++ str ":" ++ 
      pr_type_v_v8 v ++ pr_effects e ++ 
      pr_pre_condition_list prel ++ pr_post_condition_opt postl ++
      spc () ++ str "end"
  | TypePure a -> Ppconstr.pr_constr a
  | v -> str "(" ++ pr_type_v_v8 v ++ str ")"

and pr_binder = function
  | (id,BindType c) ->
      str "(" ++ pr_id id ++ str ":" ++ pr_type_v_v8 c ++ str ")"
  | (id,BindSet) ->
      str "(" ++ pr_id id ++ str ":" ++ str "Set" ++ str ")"
  | (id,Untyped) ->
      str "<<<<< TODO: Untyped binder >>>>"

let _ =
  Pptactic.declare_extra_genarg_pprule true
    (rawwit_type_v, fun _ _ -> pr_type_v_v8)
    (globwit_type_v, fun _ -> raise Not_found)
    (wit_type_v, fun _ -> raise Not_found)

(* Program printer *)

let pr_precondition pred = str "{" ++ pr_assert true pred ++ str "}" ++ spc ()

let pr_postcondition pred = str "{" ++ pr_predicate true pred ++ str "}"

let pr_invariant = function
  | None -> mt ()
  | Some c -> hov 2 (str "invariant" ++ spc ()  ++ pr_predicate false c)

let pr_variant (c1,c2) =
  Ppconstr.pr_constr c1 ++
  (try Constrextern.check_same_type c2 (ast_zwf_zero dummy_loc); mt ()
   with _ -> spc() ++ hov 0 (str "for" ++ spc () ++ Ppconstr.pr_constr c2))

let rec pr_desc = function
  | Variable id ->
      (* Unsafe: should distinguish global names and bound vars *)
      let vars = (* TODO *) Idset.empty in
      let id = try 
        snd (repr_qualid
          (snd (qualid_of_reference 
            (Constrextern.extern_reference
              dummy_loc vars (Nametab.locate (make_short_qualid id))))))
      with _ -> id in
      pr_id id
  | Acc id -> str "!" ++ pr_id id
  | Aff (id,p) -> pr_id id ++ spc() ++ str ":=" ++ spc() ++ pr_prog p
  | TabAcc (b,id,p) -> pr_id id ++ str "[" ++ pr_prog p ++ str "]"
  | TabAff (b,id,p1,p2) ->
      pr_id id ++ str "[" ++ pr_prog p1 ++ str "]" ++
      str ":=" ++ pr_prog p2
  | Seq bll -> 
      hv 0 (str "begin" ++ spc () ++ pr_block bll ++ spc () ++ str "end")
  | While (p1,inv,var,bll) ->
      hv 0 (
	hov 0 (str "while" ++ spc () ++ pr_prog p1 ++ spc () ++ str "do") ++
	brk (1,2) ++
	hv 2 (
	  str "{ " ++ 
	  pr_invariant inv ++ spc() ++
	  hov 0 (str "variant" ++ spc () ++ pr_variant var)
	  ++ str " }") ++ cut () ++
	hov 0 (pr_block bll) ++ cut () ++ 
	str "done")
  | If (p1,p2,p3) ->
      hov 1 (str "if " ++ pr_prog p1) ++ spc () ++
      hov 0 (str "then" ++ spc () ++ pr_prog p2) ++ spc () ++
      hov 0 (str "else" ++ spc () ++ pr_prog p3)
  | Lam (bl,p) ->
      hov 0 
        (str "fun" ++ spc () ++ hov 0 (prlist_with_sep cut pr_binder bl) ++ 
	 spc () ++ str "=>") ++
      pr_prog p
  | Apply ({desc=Expression e; pre=[]; post=None} as p,args) when isConst e ->
      begin match
	string_of_id (snd (repr_path (Nametab.sp_of_global (ConstRef (destConst e))))),
	args
      with
      | "Zmult", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"*" ++ pr_arg a2 ++ str ")"
      | "Zplus", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"+" ++ pr_arg a2 ++ str ")"
      | "Zminus", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"-" ++ pr_arg a2 ++ str ")"
      | "Zopp", [a] ->
	  str "( -" ++ pr_arg a ++ str ")"
      | "Z_lt_ge_bool", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"<" ++ pr_arg a2 ++ str ")"
      | "Z_le_gt_bool", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"<=" ++ pr_arg a2 ++ str ")"
      | "Z_gt_le_bool", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str">" ++ pr_arg a2 ++ str ")"
      | "Z_ge_lt_bool", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str">=" ++ pr_arg a2 ++ str ")"
      | "Z_eq_bool", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"=" ++ pr_arg a2 ++ str ")"
      | "Z_noteq_bool", [a1;a2] ->
	  str "(" ++ pr_arg a1 ++ str"<> " ++ pr_arg a2 ++ str ")"
      | _ -> 
	  str "(" ++ pr_prog p ++ spc () ++ prlist_with_sep spc pr_arg args ++
	  str ")"
      end
  | Apply (p,args) ->
      str "(" ++ pr_prog p ++ spc () ++ prlist_with_sep spc pr_arg args ++
      str ")"
  | SApp ([Variable v], args) ->
      begin match string_of_id v, args with
	| "prog_bool_and", [a1;a2] -> 
	    str"(" ++ pr_prog a1 ++ spc() ++ str"and " ++ pr_prog a2 ++str")"
	| "prog_bool_or", [a1;a2] -> 
	    str"(" ++ pr_prog a1 ++ spc() ++ str"or " ++ pr_prog a2 ++ str")"
	| "prog_bool_not", [a] ->
	    str "(not " ++ pr_prog a ++ str ")"
	| _ -> failwith "Correctness printer: TODO"
      end
  | SApp _ -> failwith "Correctness printer: TODO"
  | LetRef (v,p1,p2) ->
      hov 2 (
	str "let " ++ pr_id v ++ str " =" ++ spc () ++ str "ref" ++ spc () ++
	pr_prog p1 ++ str " in") ++
      spc () ++ pr_prog p2
  | Let (id, {desc=LetRec (f,bl,v,var,p); pre=[]; post=None },p2) when f=id ->
      hov 2 (
	str "let rec " ++ pr_id f ++ spc () ++
	hov 0 (prlist_with_sep cut pr_binder bl) ++ spc () ++
	str ":" ++ pr_type_v_v8 v ++ spc () ++
	hov 2 (str "{ variant" ++ spc () ++ pr_variant var ++ str " }") ++ 
	spc() ++ str "=" ++ spc () ++ pr_prog p ++
 	str " in") ++
      spc () ++ pr_prog p2
  | Let (v,p1,p2) ->
      hov 2 (
	str "let " ++ pr_id v ++ str " =" ++ spc () ++ pr_prog p1 ++ str" in")
      ++ spc () ++ pr_prog p2
  | LetRec (f,bl,v,var,p) ->
      str "let rec " ++ pr_id f ++ spc () ++
      hov 0 (prlist_with_sep cut pr_binder bl) ++ spc () ++
      str ":" ++ pr_type_v_v8 v ++ spc () ++
      hov 2 (str "{ variant" ++ spc () ++ pr_variant var ++ str " }") ++
      spc () ++ str "=" ++ spc () ++ pr_prog p
  | PPoint _ -> str "TODO: Ppoint" (* Internal use only *)
  | Expression c ->
      (* Numeral or "tt": use a printer which doesn't globalize *)
      Ppconstr.pr_constr
        (Constrextern.extern_constr_in_scope false "Z_scope" (Global.env()) c)
  | Debug (s,p) -> str "@" ++ Pptactic.qsnew s ++ pr_prog p

and pr_block_st = function
  | Label s -> hov 0 (str "label" ++ spc() ++ str s)
  | Assert pred -> 
      hov 0 (str "assert" ++ spc() ++ hov 0 (pr_postcondition pred))
  | Statement p -> pr_prog p

and pr_block bl = prlist_with_sep pr_semicolon pr_block_st bl

and pr_arg = function
  | Past.Term p -> pr_prog p
  | Past.Type t -> str "'" ++ pr_type_v_v8 t
  | Refarg _ -> str "TODO: Refarg" (* Internal use only *)

and pr_prog0 b { desc = desc; pre = pre; post = post } =
  hv 0 (
    prlist pr_precondition pre ++
    hov 0
      (if b & post<>None then str"(" ++ pr_desc desc ++ str")"
       else pr_desc desc)
    ++ Ppconstr.pr_opt pr_postcondition post)

and pr_prog x = pr_prog0 true x

let _ =
  Pptactic.declare_extra_genarg_pprule true
    (rawwit_program, fun _ _ a -> spc () ++ pr_prog0 false a)
    (globwit_program, fun _ -> raise Not_found)
    (wit_program, fun _ -> raise Not_found)

