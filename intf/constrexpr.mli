(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Libnames
open Misctypes
open Decl_kinds

(** {6 Concrete syntax for terms } *)

(** [constr_expr] is the abstract syntax tree produced by the parser *)

type notation = string

type explicitation =
  | ExplByPos of int * Id.t option
  | ExplByName of Id.t

type binder_kind =
  | Default of binding_kind
  | Generalized of binding_kind * binding_kind * bool
      (** Inner binding, outer bindings, typeclass-specific flag
	 for implicit generalization of superclasses *)

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (** [Some n] = proj of the n-th visible argument *)

type prim_token =
  | Numeral of Bigint.bigint (** AST representation of integer literals that appear in Coq scripts. *)
  | String of string

type raw_cases_pattern_expr =
  | RCPatAlias of Loc.t * raw_cases_pattern_expr * Id.t
  | RCPatCstr of Loc.t * Globnames.global_reference
    * raw_cases_pattern_expr list * raw_cases_pattern_expr list
  (** [CPatCstr (_, Inl c, l1, l2)] represents (@c l1) l2 *)
  | RCPatAtom of Loc.t * Id.t option
  | RCPatOr of Loc.t * raw_cases_pattern_expr list

type cases_pattern_expr =
  | CPatAlias of Loc.t * cases_pattern_expr * Id.t
  | CPatCstr of Loc.t * reference
    * cases_pattern_expr list * cases_pattern_expr list
  (** [CPatCstr (_, Inl c, l1, l2)] represents (@c l1) l2 *)
  | CPatAtom of Loc.t * reference option
  | CPatOr of Loc.t * cases_pattern_expr list
  | CPatNotation of Loc.t * notation * cases_pattern_notation_substitution
    * cases_pattern_expr list (** CPatNotation (_, n, l1 ,l2) represents
				  (notation n applied with substitution l1)
				  applied to arguments l2 *)
  | CPatPrim of Loc.t * prim_token
  | CPatRecord of Loc.t * (reference * cases_pattern_expr) list
  | CPatDelimiters of Loc.t * string * cases_pattern_expr

and cases_pattern_notation_substitution =
    cases_pattern_expr list *     (** for constr subterms *)
    cases_pattern_expr list list  (** for recursive notations *)

type instance_expr = Misctypes.glob_level list

(** AST representation of a term. *)

(* These values are part of the abstract syntax tree.
 * The concrete syntax is described in Section 1.2 of the Reference manual.
 * The concrete syntax is defined by 'lconstr' non-terminal in 'parsing/g_constr.ml4'.
 * These values are returned by 'Pcoq.parse_string Pcoq.Constr.lconstr' function.
 *
 * So e.g.:
 *
 *   Pcoq.parse_string Pcoq.Constr.lconstr "foo"
 *
 * returns
 *
 *   CRef (Ident ((0,3), foo)) None
 *)
type constr_expr =

  (* Qualified/unqualified identifiers.
   *
   * Examples:
   *
   *    O
   *    Datatypes.O
   *    Coq.Init.Datatypes.O
   *)
  | CRef of reference              (* Identifier itself. *)
          * instance_expr option   (* "None" ... under normal circumstances.
                                    * "Some _" ... when dealing with universe polymorphism.
                                    *)

  (* term ::= fix <fix_expr>
   *        | fix <fix_expr_1> with <fix_expr_2> ... with <fix_expr_N> for <ident_I>
   *)
  | CFix of Loc.t          (* position of the "fix" keyword *)
          * Id.t located   (* <ident_I> *)
          * fix_expr list  (* [<fix_expr_1>; <fix_expr_2>; ... ; <fix_expr_N>] *)

  (* term ::= cofix <cofix_expr>
   *        | cofix <cofix_expr_1> with <cofix_expr_2> ... with <cofix_expr_N> for <ident_I>
   *)
  | CCoFix of Loc.t            (* position of the "cofix" keyword *)
            * Id.t located     (* <ident_I> *)
            * cofix_expr list  (* [<cofix_expr_1>; <cofix_expr_2>; ... ; <cofix_expr_N>] *)

  (* term ::= forall <binders>, <constr> *)
  | CProdN of Loc.t             (* position of the "forall" keyword *)
            * binder_expr list  (* <binders> *)
            * constr_expr       (* <constr> *)

  (* term ::= fun <binders> => <constr> *)
  | CLambdaN of Loc.t             (* position of the "fun" keyword *)
              * binder_expr list  (* <binders> *)
              * constr_expr       (* <constr> *)

  (* term ::= let <ident> := <constr_A> in <constr_B> *)
  | CLetIn of Loc.t            (* position of the "let" keyword *)
            * Name.t located   (* <ident> *)
            * constr_expr      (* <constr_A> *)
            * constr_expr      (* <constr_B> *)

  (* term ::= @ <ident> <constr_1> ... <constr_N>
   *        | ...
   *)
  | CAppExpl of Loc.t                   (* position of <ident> *)
              * (proj_flag              (* None *)
                * reference             (* <ident> *)
                * instance_expr option  (* None *)
                )
              * constr_expr list        (* [<constr_1>; ...; <constr_N>] *)

  (* term ::= <constr_0> <constr_1> ... <constr_N>
   *             (* CApp (_, (None, <constr_0>), [<constr_1>, None; ...; <constr_N>, None]) *)
   *
   *        | <constr_0> (<ident_1> := <constr_1>) ... (<ident_N> := <constr_N>)
   *             (* CApp (_, (None, <constr_0), [<constr_1>, Some (ByName <ident_1>);
   *                                             ...
   *                                             <constr_N>, Some (ByName <ident_N>)]) *)
   *
   *        | ...
   *)
  | CApp of Loc.t
          * (proj_flag * constr_expr)
          * (constr_expr * explicitation located option) list

  (* term := {| <ident_1> := <constr_1> ; ... ; <ident_N> := <constr_N> |} *)
  | CRecord of Loc.t
             * (reference     (* <ident_I> *)
               * constr_expr  (* <constr_I> *)
               ) list

  (* term := match <case_expr_1>, ..., <case_expr_N> [return <constr_R>] with
   *         <branch_expr_1>
   *         ...
   *         <branch_expr_M>
   *         end
   *
   *       | ...
   *)
  | CCases of Loc.t                (* location of the "match" keyword *)
            * case_style           (* RegularStyle *)
            * constr_expr option   (* None | Some <constr_R> *)
            * case_expr list       (* [<case_expr_1>; ... ; <case_expr_N>] *)
            * branch_expr list     (* [<branch_expr_1>; ...; <branch_expr_M>] *)

  | CLetTuple of Loc.t * Name.t located list * (Name.t located option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of Loc.t * constr_expr * (Name.t located option * constr_expr option)
      * constr_expr * constr_expr 

  (* Representation of '_' characters that appear in the original terms.
   * Those '_' characters either represent terms that user expects Coq will infer during pre-typing phase,
   * or they represent wildcards in patterns.
   *)
  | CHole of Loc.t * Evar_kinds.t option * intro_pattern_naming_expr * Genarg.raw_generic_argument option

  | CPatVar of Loc.t * patvar
  | CEvar of Loc.t * Glob_term.existential_name * (Id.t * constr_expr) list   (* existential variables *)
  | CSort of Loc.t * glob_sort   (* representation of sorts (i.e. 'Prop', 'Set', and 'Type' *)

  (* (<constr_expr> : constr_expr cast_type) *)
  | CCast of Loc.t * constr_expr * constr_expr cast_type

  (* Representation of terms that take advantage of user-defined 'notations'. E.g.:
   *
   *  2+3  --->  CNotation loc "_ + _" ([CPrim _ (Numeral 2); CPrim _ (Numeral 3)],
   *                                    [],
   *                                    []))
   *)
  | CNotation of Loc.t * notation * constr_notation_substitution

  | CGeneralization of Loc.t * binding_kind * abstraction_kind option * constr_expr

  (* Representation of 'primitive tokens' (in other words 'literals'). E.g.:
   *
   *   42     --->  CPrim _ (Numeral 42)
   *   "foo"  --->  CPrim (280,285) (String "foo")
   *)
  | CPrim of Loc.t * prim_token

  (* Representation of 'interpretation scope'. E.g.:
   *
   *   0%nat  --->  CDelimiters _ "nat" (CPrim _ (Numeral 0))
   *   0%Z    --->  CDelimiters _ "Z" (CPrim _ (Numeral 0))
   *)
  | CDelimiters of Loc.t * string * constr_expr

and case_expr =
  constr_expr * (Name.t located option * cases_pattern_expr option)

and branch_expr =
  Loc.t * cases_pattern_expr list located list * constr_expr

(* representation of bindings (of products and lambda-expressions) *)
and binder_expr = Name.t located list  (* names of bound variables *)
                * binder_kind          (* implicit bindings / explicit bindings *)
                * constr_expr          (* type of bound variables *)

(* <fix_expr> ::= <ident> <binders> [<annotation>] [: <termA>] := <termB> *)
and fix_expr = Id.t located       (* <ident> *)
             * fix_annotation     (* <annotation> *)
             * local_binder list  (* <binders> *)
             * constr_expr        (* <termA> *)
             * constr_expr        (* <termB> *)

(* <cofix_expr> ::= <ident> [: <termA>] := <termB> *)
and cofix_expr = Id.t located       (* <ident> *)
               * local_binder list  (* <binders> *)
               * constr_expr        (* <termA> *)
               * constr_expr        (* <termB> *)

(* fix_annotation ::=                                          (* None, CStructRec *)
 *                  | { struct <ident> }                       (* Some <ident>, CStructRec *)
 *                  | { wf <constr> }                          (* None, CWfRec <constr> *)
 *                  | { wf <constr> <ident> }                  (* Some <ident>, CWfRec <constr> *)
 *                  | { measure <constr>}                      (* None, CMeasureRec (<constr>, None) *)
 *                  | { measure <constr> <ident> }             (* Some <ident>, CMeasureRec (<constr>, None) *)
 *                  | { measure <constrA> <ident> <constrB> }  (* Some <ident>, CMeasureRec (<constrA>, Some <constrB>) *)
 *)
and fix_annotation = Id.t located option
                   * recursion_order_expr

and recursion_order_expr =
  | CStructRec
  | CWfRec of constr_expr
  | CMeasureRec of constr_expr * constr_expr option (** measure, relation *)

(* <local_binder> ::= <ident>                                   (* LocalRawAssum ([<ident>], Default Explicit, CHole _) *)
 *                  | ( <ident_1> ... <ident_N> : <constr> )    (* LocalRawAssum ([<ident_1>; ...; <ident_N>], Default Explicit, <constr>) *)
 *                  | ( <ident> := <constr> )                   (* LocalRawDef (<ident>, <constr>) *)
 *                  | ( <ident_1> : <constr_A> := <constr_B> )  (* LocalRawDef (<ident>, CCast(_, <constr_B>, CastConv <constr_A>)) *)
 *                  | { <ident_1> ... <ident_N> }               (* LocalRawAssum ([<ident_1>; ...; <ident_N>], Default Implicit, CHole _) *)
 *                  | { <ident_1> ... <ident_N> : <constr> }    (* LocalRawAssum ([<ident_1>; ...; <ident_N>], Default Implicit, <constr>) *)
 *                  | ...
 *)
and local_binder =
  | LocalRawDef of Name.t located * constr_expr
  | LocalRawAssum of Name.t located list * binder_kind * constr_expr

and constr_notation_substitution =
    constr_expr list *      (** for constr subterms *)
    constr_expr list list * (** for recursive notations *)
    local_binder list list (** for binders subexpressions *)

type typeclass_constraint = Name.t located * binding_kind * constr_expr

and typeclass_context = typeclass_constraint list

type constr_pattern_expr = constr_expr

(** Concrete syntax for modules and module types *)

type with_declaration_ast =
  | CWith_Module of Id.t list located * qualid located
  | CWith_Definition of Id.t list located * constr_expr

type module_ast =
  | CMident of qualid located
  | CMapply of Loc.t * module_ast * module_ast
  | CMwith of Loc.t * module_ast * with_declaration_ast
