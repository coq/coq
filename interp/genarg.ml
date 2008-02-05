(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* arnaud: experimental *)

open Pp
open Util
open Names
open Nameops
open Nametab
open Rawterm
open Topconstr
open Term
open Evd

type argument_type =
  (* Basic types *)
  | BoolArgType
  | IntArgType
  | IntOrVarArgType
  | StringArgType
  | PreIdentArgType
  | IntroPatternArgType
  | IdentArgType
  | VarArgType
  | RefArgType
  (* Specific types *)
  | SortArgType
  | ConstrArgType
  | ConstrMayEvalArgType
  | QuantHypArgType
  | OpenConstrArgType of bool
  | ConstrWithBindingsArgType
  | BindingsArgType
  | RedExprArgType
  | List0ArgType of argument_type
  | List1ArgType of argument_type
  | OptArgType of argument_type
  | PairArgType of argument_type * argument_type
  | ExtraArgType of string
  (* wildcard type *)
  | AnyArgType

exception DynamicTypeError

let rec matching p t =
  match p,t with
  | AnyArgType, _ -> [t]
  | _, AnyArgType -> raise DynamicTypeError
  | List0ArgType p', List0ArgType t' 
  | List1ArgType p', List1ArgType t'
  | OptArgType p', OptArgType t' -> matching p' t'
  | PairArgType (pl,pr) , PairArgType (tl,tr) -> 
      (matching pl tl)@(matching pr tr)
  | _,_ -> if p=t then [] else raise DynamicTypeError

type 'a and_short_name = 'a * identifier located option
type 'a or_by_notation = AN of 'a | ByNotation of loc * string

type rawconstr_and_expr = rawconstr * constr_expr option
type open_constr_expr = unit * constr_expr
type open_rawconstr = unit * rawconstr_and_expr

type 'a with_ebindings = 'a * open_constr bindings

(* Dynamics but tagged by a type expression *)

type 'a generic_argument = argument_type * Obj.t

let dyntab = ref ([] : string list)

type raw = <constr:constr_expr; 
            reference:Libnames.reference;
	    sort:rawsort;
	    may_eval:(constr_expr,Libnames.reference or_by_notation) may_eval;
	    open_constr:open_constr_expr;
	    with_bindings:constr_expr with_bindings;
	    bindings:constr_expr bindings;
	    red_expr:(constr_expr,Libnames.reference or_by_notation) red_expr_gen>
type glob = <constr:rawconstr_and_expr; 
             reference:Libnames.global_reference located or_var;
	     sort:rawsort;
	     may_eval:(rawconstr_and_expr,evaluable_global_reference and_short_name or_var) may_eval;
	     open_constr:open_rawconstr;
	     with_bindings:rawconstr_and_expr with_bindings;
	     bindings:rawconstr_and_expr bindings;
	     red_expr:(rawconstr_and_expr,evaluable_global_reference and_short_name or_var) red_expr_gen>
type typed = <constr:open_constr; 
	      reference:Libnames.global_reference;
	      sort:sorts;
	      may_eval:constr;
	      open_constr:open_constr;
	      with_bindings:constr with_ebindings;
	      bindings:open_constr bindings;
	      red_expr:(constr,evaluable_global_reference) red_expr_gen>

type 'a level = 'a -> 'a

(* spoof stuff for level introduction*)

let rlevel = fun x -> x
let glevel = fun x -> x
let tlevel = fun x -> x

type ('a,'b) abstract_argument_type = argument_type

let create_arg s =
  if List.mem s !dyntab then
    anomaly ("Genarg.create: already declared generic argument " ^ s);
  dyntab := s :: !dyntab;
  let t = ExtraArgType s in
  (t,t,t)

let exists_argtype s = List.mem s !dyntab

type intro_pattern_expr =
  | IntroOrAndPattern of case_intro_pattern_expr
  | IntroWildcard
  | IntroIdentifier of identifier
  | IntroAnonymous
  | IntroFresh of identifier
and case_intro_pattern_expr = intro_pattern_expr list list

let rec pr_intro_pattern = function
  | IntroOrAndPattern pll -> pr_case_intro_pattern pll
  | IntroWildcard -> str "_"
  | IntroIdentifier id -> pr_id id
  | IntroAnonymous -> str "?"
  | IntroFresh id -> str "?" ++ pr_id id

and pr_case_intro_pattern = function
  | [pl] ->
      str "(" ++ hv 0 (prlist_with_sep pr_coma pr_intro_pattern pl) ++ str ")"
  | pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_bar (prlist_with_sep spc pr_intro_pattern) pll)
      ++ str "]"

type something (* meant to be {t:Type & t}  in Coq syntax. i.e. : any object
		  which has a type *)

let wit_any _ = AnyArgType

let wit_bool _ = BoolArgType

let wit_int _ = IntArgType

let wit_int_or_var _ = IntOrVarArgType

let wit_string _ = StringArgType

let wit_pre_ident _ = PreIdentArgType

let wit_intro_pattern _ = IntroPatternArgType

let wit_ident _ = IdentArgType

let wit_var _ = VarArgType

let wit_ref _ = RefArgType

let wit_quant_hyp _ = QuantHypArgType

let wit_sort _ = SortArgType

let wit_constr _ = ConstrArgType

let wit_constr_may_eval _ = ConstrMayEvalArgType

let wit_open_constr_gen _ b = OpenConstrArgType b

let wit_open_constr l = wit_open_constr_gen l false

let wit_casted_open_constr l = wit_open_constr_gen l true

let wit_constr_with_bindings _ = ConstrWithBindingsArgType

let wit_bindings _ = BindingsArgType

let wit_red_expr _ = RedExprArgType

let wit_list0 t = List0ArgType t

let wit_list1 t = List1ArgType t

let wit_opt t = OptArgType t

let wit_pair t1 t2 = PairArgType (t1,t2)

let in_gen t o = (t,Obj.repr o)
let out_gen t (t',o) = let _ = matching t t' in Obj.magic o(* arnaud: essai if t = t' then Obj.magic o else failwith "out_gen"*)
let genarg_tag (s,_) = s

let fold_list0 f g =
f g  

(*arnaud: essaifunction
  | (List0ArgType t, l) ->
      List.fold_right (fun x -> f (in_gen t x)) (Obj.magic l)
  | _ -> failwith "Genarg: not a list0" *)

let fold_list1 f = function
  | (List1ArgType t, l) ->
      List.fold_right (fun x -> f (in_gen t x)) (Obj.magic l)
  | _ -> failwith "Genarg: not a list1"

let fold_opt f a = function
  | (OptArgType t, l) ->
      (match Obj.magic l with
	| None -> a
	| Some x -> f (in_gen t x))
  | _ -> failwith "Genarg: not a opt"

let fold_pair f = function
  | (PairArgType (t1,t2), l) ->
      let (x1,x2) = Obj.magic l in
      f (in_gen t1 x1) (in_gen t2 x2)
  | _ -> failwith "Genarg: not a pair"

let app_list0 f = function
  | (List0ArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (List.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not a list0"

let app_list1 f = function
  | (List1ArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (List.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not a list1"

let app_opt f = function
  | (OptArgType t as u, l) ->
      let o = Obj.magic l in
      (u, Obj.repr (Option.map (fun x -> out_gen t (f (in_gen t x))) o))
  | _ -> failwith "Genarg: not an opt"

let app_pair f1 f2 = function
  | (PairArgType (t1,t2) as u, l) ->
      let (o1,o2) = Obj.magic l in
      let o1 = out_gen t1 (f1 (in_gen t1 o1)) in
      let o2 = out_gen t2 (f2 (in_gen t2 o2)) in
      (u, Obj.repr (o1,o2))
  | _ -> failwith "Genarg: not a pair"

let unquote x = x

type an_arg_of_this_type = Obj.t

let in_generic t x = (t, Obj.repr x)
