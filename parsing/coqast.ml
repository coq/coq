(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Names
open Libnames
(*i*)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nmeta of loc * string
  | Nvar of loc * identifier
  | Slam of loc * identifier option * t
  | Smetalam of loc * string * t
  | Num of loc * int
  | Str of loc * string
  | Id of loc * string
  | Path of loc * kernel_name
  | Dynamic of loc * Dyn.t

type the_coq_ast = t

let subst_meta bl ast =
  let rec aux = function
    | Node (_,"META", [Num(_, n)]) -> List.assoc n bl
    | Node(loc, node_name, args) -> 
	Node(loc, node_name, List.map aux args)
    | Slam(loc, var, arg) -> Slam(loc, var, aux arg)
    | Smetalam(loc, var, arg) -> Smetalam(loc, var, aux arg)
    | other -> other
  in 
  aux ast

let rec collect_metas = function
  | Node (_,"META", [Num(_, n)]) -> [n]
  | Node(_, _, args) -> List.concat (List.map collect_metas args)
  | Slam(loc, var, arg) -> collect_metas arg
  | Smetalam(loc, var, arg) -> collect_metas arg
  | _ -> []

(* Hash-consing *)
module Hloc = Hashcons.Make(
  struct
    type t = loc
    type u = unit
    let equal (b1,e1) (b2,e2) = b1=b2 & e1=e2
    let hash_sub () x = x
    let hash = Hashtbl.hash
  end)

module Hast = Hashcons.Make(
  struct
    type t = the_coq_ast
    type u = 
	(the_coq_ast -> the_coq_ast) *
	((loc -> loc) * (string -> string)
	 * (identifier -> identifier) * (kernel_name -> kernel_name))
    let hash_sub (hast,(hloc,hstr,hid,hsp)) = function
      | Node(l,s,al) -> Node(hloc l, hstr s, List.map hast al)
      | Nmeta(l,s) -> Nmeta(hloc l, hstr s)
      | Nvar(l,s) -> Nvar(hloc l, hid s)
      | Slam(l,None,t) -> Slam(hloc l, None, hast t)
      | Slam(l,Some s,t) -> Slam(hloc l, Some (hid s), hast t)
      | Smetalam(l,s,t) -> Smetalam(hloc l, hstr s, hast t)
      | Num(l,n) -> Num(hloc l, n)
      | Id(l,s) -> Id(hloc l, hstr s)
      | Str(l,s) -> Str(hloc l, hstr s)
      | Path(l,d) -> Path(hloc l, hsp d)
      | Dynamic(l,d) -> Dynamic(hloc l, d)
    let equal a1 a2 =
      match (a1,a2) with
        | (Node(l1,s1,al1), Node(l2,s2,al2)) ->
            (l1==l2 & s1==s2 & List.length al1 = List.length al2)
            & List.for_all2 (==) al1 al2
        | (Nmeta(l1,s1), Nmeta(l2,s2)) -> l1==l2 & s1==s2
        | (Nvar(l1,s1), Nvar(l2,s2)) -> l1==l2 & s1==s2
        | (Slam(l1,None,t1), Slam(l2,None,t2)) -> l1==l2 & t1==t2
        | (Slam(l1,Some s1,t1), Slam(l2,Some s2,t2)) ->l1==l2 & s1==s2 & t1==t2
        | (Smetalam(l1,s1,t1), Smetalam(l2,s2,t2)) -> l1==l2 & s1==s2 & t1==t2
        | (Num(l1,n1), Num(l2,n2)) -> l1==l2 & n1=n2
        | (Id(l1,s1), Id(l2,s2)) -> l1==l2 & s1==s2
        | (Str(l1,s1),Str(l2,s2)) -> l1==l2 & s1==s2
        | (Path(l1,d1), Path(l2,d2)) -> (l1==l2 & d1==d2)
        | _ -> false
    let hash = Hashtbl.hash
  end)

let hcons_ast (hstr,hid,hpath) =
  let hloc = Hashcons.simple_hcons Hloc.f () in
  let hast = Hashcons.recursive_hcons Hast.f (hloc,hstr,hid,hpath) in
  (hast,hloc)

(*
type 'vernac_ast raw_typed_ast =
  | PureAstNode of t
  | AstListNode of t list
  | PureAstNode of t
  | TacticAstNode of tactic_expr
  | VernacAstNode of 'vernac_ast

type entry_type =
  | PureAstType
  | AstListType
  | VernacAstType
  | TacticAstType
  | VernacAtomAstType
  | DynamicAstType
  | QualidAstType
  | ConstrAstType
  | BinderAstType
  | ThmTokAstType
  | BindingListAstType

type astpat =
  | Pquote of t
  | Pmeta of string * tok_kind
  | Pnode of string * patlist
  | Pslam of identifier option * astpat
  | Pmeta_slam of string * astpat

and patlist =
  | Pcons of astpat * patlist
  | Plmeta of string
  | Pnil

type 'a syntax_rule = string * 'a raw_typed_ast * t unparsing_hunk list
type 'a raw_syntax_entry_ast = precedence * 'a syntax_rule list

type grammar_associativity = Gramext.g_assoc option
type 'a raw_grammar_action =
  | SimpleAction of loc * 'a raw_typed_ast
  | CaseAction of loc *
     'a raw_grammar_action * entry_type option
      * (t list * 'a raw_grammar_action) list
type grammar_production =
    VTerm of string | VNonTerm of loc * nonterm * string option
type 'a grammar_rule = string * grammar_production list * 'a raw_grammar_action
type 'a raw_grammar_entry_ast = 
    (loc * string) * entry_type option * grammar_associativity * 'a grammar_rule list

type evaluable_global_reference_ast =
  | AEvalVarRef of identifier
  | AEvalConstRef of section_path

type flags_ast = int

type red_expr_ast = (t,t,t) Rawterm.red_expr_gen

type vernac_arg = 
  | VARG_VARGLIST of vernac_arg list
  | VARG_STRING of string
  | VARG_NUMBER of int
  | VARG_NUMBERLIST of int list
  | VARG_IDENTIFIER of identifier
  | VARG_QUALID of Nametab.qualid
  | VCALL of string * vernac_arg list
  | VARG_CONSTR of t
  | VARG_CONSTRLIST of t list
  | VARG_TACTIC of tactic_expr
  | VARG_REDEXP of red_expr_ast
  | VARG_BINDER of identifier list * t
  | VARG_BINDERLIST of (identifier list * t) list
  | VARG_AST of t
  | VARG_ASTLIST of t list
  | VARG_UNIT
  | VARG_DYN of Dyn.t

type def_kind = DEFINITION | LET | LOCAL | THEOREM | LETTOP | DECL | REMARK
  | FACT | LEMMA
  | COERCION | LCOERCION | OBJECT | LOBJECT | OBJCOERCION | LOBJCOERCION
  | SUBCLASS | LSUBCLASS

open Nametab

type declaration_hook = strength -> global_reference -> unit
let add_coercion = ref (fun _ _ -> ())
let add_subclass = ref (fun _ _ -> ())
let add_object = ref (fun _ _ -> ())

type constr_ast = t
type sort_expr = t

type simple_binders = identifier * constr_ast
type constructor_ast = identifier * constr_ast
type inductive_ast =
    identifier *  simple_binders list * constr_ast * constructor_ast list
type fixpoint_ast =
    identifier * simple_binders list * constr_ast * constr_ast
type cofixpoint_ast =
    identifier * constr_ast * constr_ast

type local_decl_expr =
  | AssumExpr of identifier * constr_ast
  | DefExpr of identifier * constr_ast * constr_ast option

type vernac_atom_ast =
  (* Syntax *) 
  | VernacGrammar of string * vernac_ast raw_grammar_entry_ast list
  | VernacSyntax of string * vernac_ast raw_syntax_entry_ast list
  | VernacInfix of grammar_associativity * int * string * t
  | VernacDistfix of grammar_associativity * int * string * t
  (* Gallina *)
  | VernacDefinition of (bool * strength) * identifier * t option * constr_ast * constr_ast option * declaration_hook
  | VernacStartProof of (bool * strength) * identifier * constr_ast * bool * declaration_hook
  | VernacEndProof of bool * strength option * identifier option
  | VernacAssumption of strength * (identifier list * constr_ast) list
  | VernacInductive of bool * inductive_ast list
  | VernacFixpoint of fixpoint_ast list
  | VernacCoFixpoint of cofixpoint_ast list
  (* Gallina extensions *)
  | VernacRecord of bool * identifier * simple_binders list * sort_expr * identifier option * (bool * local_decl_expr) list

  (* Commands *)
  | TacticDefinition of loc * (identifier * tactic_expr) list
  | VernacSetOpacity of bool * (loc * identifier list) list
  | VernacSolve of int * tactic_expr
  (* For temporary compatibility *)
  | ExtraVernac of t
  (* For extension *)
  | VernacExtend of string * vernac_arg list
  (* For actions in Grammar and patterns in Syntax rules *)
  | VernacMeta of loc * string

and located_vernac_atom_ast = loc * vernac_atom_ast

and vernac_ast =
  | VTime of located_vernac_atom_ast
  | VLoad of bool * string
  | VernacList of located_vernac_atom_ast list
  | VernacVar of identifier

type pat = vernac_ast raw_pat
type typed_ast = vernac_ast raw_typed_ast
type grammar_action = vernac_ast raw_grammar_action
type grammar_entry_ast = vernac_ast raw_grammar_entry_ast
type syntax_entry_ast = vernac_ast raw_syntax_entry_ast

*)
