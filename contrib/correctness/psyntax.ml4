(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Options
open Names
open Nameops
open Vernacentries
open Reduction
open Term

open Prename
open Pmisc
open Putil
open Ptype
open Past
open Penv
open Pmonad


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
    let ident = gec "ident"
    let wf_arg = gec "wf_arg"
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
  G_zsyntax.z_of_string true n Ast.dummy_loc

let constr_of_int n =
  Astterm.interp_constr Evd.empty (Global.env ()) (ast_of_int n)

let ast_constant loc s = <:ast< (QUALID ($VAR $s)) >>

let conj_assert {a_name=n;a_value=a} {a_value=b} = 
  let loc = Ast.loc a in
  let et = ast_constant loc "and" in
  { a_value = <:ast< (APPLIST $et $a $b) >>; a_name = n }

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

let ast_zwf_zero loc =
  let zwf = ast_constant loc "Zwf" and zero = ast_constant loc "ZERO" in
    <:ast< (APPLIST $zwf $zero) >>

(* program -> Coq AST *)

let bdize c = 
  let env = 
    Global.env_of_context (Pcicenv.cci_sign_of Prename.empty_ren Penv.empty)
  in
  Termast.ast_of_constr true env c

let rec coqast_of_program loc = function
  | Variable id -> let s = string_of_id id in <:ast< ($VAR $s) >>
  | Acc id -> let s = string_of_id id in <:ast< ($VAR $s) >>
  | Apply (f,l) -> 
      let f = coqast_of_program f.loc f.desc in
      let args = List.map 
		   (function Term t -> coqast_of_program t.loc t.desc
		      | _ -> invalid_arg "coqast_of_program") l
      in
      <:ast< (APPLIST $f ($LIST $args)) >>
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
  let zplus = ast_constant loc "Zplus" in
  let un = ast_of_int "1" in
  <:ast< (APPLIST $zplus $ast $un) >>

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
      let zle = ast_constant loc "Zle" in
      let i_le_sv2 = <:ast< (APPLIST $zle ($VAR $i) $succ_v2) >> in
      conj_assert {a_value=i_le_sv2;a_name=inv.a_name} inv
    in
    { desc = If(test,br_t,br_f); loc = loc; 
      pre = [pre_of_assert false inv']; post = Some post; info = () } 
  in
  let bl = 
    let typez = ast_constant loc "Z" in
    [(id_of_string i, BindType (TypePure typez))] 
  in
  let fv1 = without_effect loc (Apply (var_f, [Term v1])) in
  let v = TypePure (ast_constant loc "unit") in
  let var = 
    let zminus = ast_constant loc "Zminus" in
    let a = <:ast< (APPLIST $zminus $succ_v2 ($VAR $i)) >> in
    (a, ast_zwf_zero loc)
  in
  Let (f, without_effect loc (LetRec (f,bl,v,var,e1)), fv1)

let mk_prog loc p pre post =
  { desc = p.desc; 
    pre = p.pre @ pre; 
    post = conj (p.post,post); 
    loc = loc; 
    info = () }

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
  ident:
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
  wf_arg:
    [ [ "{"; IDENT "wf"; c = Constr.constr; IDENT "for";
	w = Constr.constr; "}" ->
	  Wf (c,w)
      | "{"; IDENT "wf"; n = INT; "}" ->
	  RecArg (int_of_string n) ] ]
  ;
  invariant:
    [ [ IDENT "invariant"; c = predicate -> c ] ]
  ;
  variant:
    [ [ c = Constr.constr; IDENT "for"; r = Constr.constr -> (c, r)
      | c = Constr.constr -> (c, ast_zwf_zero loc) ] ]
  ;
  END
;;

let (in_prog,out_prog) = Dyn.create "PROGRAMS-PROG"
let (in_typev,out_typev) = Dyn.create "PROGRAMS-TYPEV"

open Pp
open Util
open Himsg
open Vernacinterp
open Declare

let is_assumed global ids =
  if List.length ids = 1 then
    msgnl (str (if global then "A global variable " else "") ++ 
	     pr_id (List.hd ids) ++ str " is assumed")
  else
    msgnl (str (if global then "Some global variables " else "") ++
	     prlist_with_sep (fun () -> (str ", ")) pr_id ids ++
	     str " are assumed")

let add = vinterp_add

let _ = add "CORRECTNESS"
     (function
	 [ VARG_STRING s; VARG_DYN d ] -> 
	   fun () -> Ptactic.correctness s (out_prog d) None
       | [ VARG_STRING s; VARG_DYN d; VARG_TACTIC t ] ->
	   let tac = Tacinterp.interp t in
	   fun () -> Ptactic.correctness s (out_prog d) (Some tac)
       | _ -> assert false)

let _ = 
  add "SHOWPROGRAMS"
    (function
       | [] -> 
	   (fun () ->
	      fold_all 
		(fun (id,v) _ -> 
		   msgnl (pr_id id ++ str " : " ++ 
			    hov 2 (match v with TypeV v -> pp_type_v v
				     | Set -> (str "Set")) ++
			    fnl ()))
		Penv.empty ())
       | _ -> assert false)

let id_of_varg = function VARG_IDENTIFIER id -> id | _ -> assert false
    
let _ = 
  add "PROGVARIABLE"
    (function
       | [ VARG_VARGLIST l; VARG_DYN d ] ->
	   (fun () ->
	      let ids = List.map id_of_varg l in
	      List.iter
		(fun id -> if Penv.is_global id then
		   Util.errorlabstrm "PROGVARIABLE"
		     (str"Clash with previous constant " ++ pr_id id))
		ids;
	      let v = out_typev d in
	      Pdb.check_type_v (all_refs ()) v;
	      let env = empty in
	      let ren = update empty_ren "" [] in
	      let v = Ptyping.cic_type_v env ren v in
	      if not (is_mutable v) then begin
		let c =
		  Safe_typing.ParameterEntry (trad_ml_type_v ren env v),
		  Declare.NeverDischarge in
		List.iter 
		  (fun id -> ignore (Declare.declare_constant id c)) ids;
		if_verbose (is_assumed false) ids
	      end;
	      if not (is_pure v) then begin
		List.iter (fun id -> ignore (Penv.add_global id v None)) ids;
		if_verbose (is_assumed true) ids
	      end)
       | _ -> assert false)

open Vernac

GEXTEND Gram
  Pcoq.Vernac_.vernac:
  [ [ IDENT "Global"; "Variable"; 
      l = LIST1 ident SEP ","; ":"; t = type_v; "." ->
	let idl = List.map Ast.nvar l in
	let d = Ast.dynamic (in_typev t) in
	  <:ast< (PROGVARIABLE (VERNACARGLIST ($LIST $idl)) (VERNACDYN $d)) >>

    | IDENT "Show"; IDENT "Programs"; "." ->
	<:ast< (SHOWPROGRAMS) >>

    | IDENT "Correctness"; s = IDENT; p = Programs.program; "." ->
	let d = Ast.dynamic (in_prog p) in
	let str = Ast.string s in
	<:ast< (CORRECTNESS $str (VERNACDYN $d)) >>

    | IDENT "Correctness"; s = IDENT; p = Programs.program; ";";
      tac = Tactic.tactic; "." ->
	let d = Ast.dynamic (in_prog p) in
	let str = Ast.string s in
	<:ast< (CORRECTNESS $str (VERNACDYN $d) (TACTIC $tac)) >> ] ];
 END
;;

