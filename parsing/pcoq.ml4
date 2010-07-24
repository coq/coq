(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo pa_macro.cmo" i*)

(*i $Id$ i*)

open Pp
open Util
open Names
open Extend
open Libnames
open Rawterm
open Topconstr
open Genarg
open Tacexpr
open Extrawit
open Ppextend

(* The parser of Coq *)

IFDEF CAMLP5 THEN

module L =
  struct
    type te = string * string
    let lexer = Lexer.lexer
  end

module G = Grammar.GMake(L)

ELSE

module L =
  struct
    let lexer = Lexer.lexer
  end

module G = Grammar.Make(L)

END

let grammar_delete e pos reinit rls =
  List.iter
    (fun (n,ass,lev) ->

      (* Caveat: deletion is not the converse of extension: when an
	 empty level is extended, deletion removes the level instead
	 of keeping it empty. This has an effect on the empty levels 8,
	 99 and 200. We didn't find a good solution to this problem
	 (e.g. using G.extend to know if the level exists results in a
	 printed error message as side effect). As a consequence an
	 extension at 99 or 8 (and for pattern 200 too) inside a section
         corrupts the parser. *)

      List.iter (fun (pil,_) -> G.delete_rule e pil) (List.rev lev))
    (List.rev rls);
  if reinit <> None then
    let lev = match pos with Some (Gramext.Level n) -> n | _ -> assert false in
    let pos =
      if lev = "200" then Gramext.First
      else Gramext.After (string_of_int (int_of_string lev + 1)) in
    G.extend e (Some pos) [Some lev,reinit,[]];

(* grammar_object is the superclass of all grammar entries *)
module type Gramobj =
sig
  type grammar_object
  val weaken_entry : 'a G.Entry.e -> grammar_object G.Entry.e
end

module Gramobj : Gramobj =
struct
  type grammar_object = Obj.t
  let weaken_entry e = Obj.magic e
end

type entry_type = argument_type
type grammar_object = Gramobj.grammar_object
type typed_entry = argument_type * grammar_object G.Entry.e
let in_typed_entry t e = (t,Gramobj.weaken_entry e)
let type_of_typed_entry (t,e) = t
let object_of_typed_entry (t,e) = e
let weaken_entry x = Gramobj.weaken_entry x

module type Gramtypes =
sig
  open Decl_kinds
  val inGramObj : 'a raw_abstract_argument_type -> 'a G.Entry.e -> typed_entry
  val outGramObj : 'a raw_abstract_argument_type -> typed_entry -> 'a G.Entry.e
end

module Gramtypes : Gramtypes =
struct
  let inGramObj rawwit = in_typed_entry (unquote rawwit)
  let outGramObj (a:'a raw_abstract_argument_type) o =
    if type_of_typed_entry o <> unquote a
      then anomaly "outGramObj: wrong type";
    (* downcast from grammar_object *)
    Obj.magic (object_of_typed_entry o)
end

open Gramtypes

type camlp4_rule =
    Compat.token Gramext.g_symbol list * Gramext.g_action

type camlp4_entry_rules =
    (* first two parameters are name and assoc iff a level is created *)
    string option * Gramext.g_assoc option * camlp4_rule list

type ext_kind =
  | ByGrammar of
      grammar_object G.Entry.e * Gramext.position option *
      camlp4_entry_rules list * Gramext.g_assoc option
  | ByGEXTEND of (unit -> unit) * (unit -> unit)

let camlp4_state = ref []

(* The apparent parser of Coq; encapsulate G to keep track of the
   extensions. *)
module Gram =
  struct
    include G
    let extend e pos rls =
      camlp4_state :=
      (ByGEXTEND ((fun () -> grammar_delete e pos None rls),
                  (fun () -> G.extend e pos rls)))
      :: !camlp4_state;
      G.extend e pos rls
    let delete_rule e pil =
      (* spiwack: if you use load an ML module which contains GDELETE_RULE
	  in a section, God kills a kitty. As it would corrupt remove_grammars.
          There does not seem to be a good way to undo a delete rule. As deleting
	  takes fewer arguments than extending. The production rule isn't returned
	  by delete_rule. If we could retrieve the necessary information, then
	  ByGEXTEND provides just the framework we need to allow this in section.
	  I'm not entirely sure it makes sense, but at least it would be more correct.
          *)
      G.delete_rule e pil
  end


let camlp4_verbosity silent f x =
  let a = !Gramext.warning_verbose in
  Gramext.warning_verbose := silent;
  f x;
  Gramext.warning_verbose := a

(* This extension command is used by the Grammar constr *)

let grammar_extend te pos reinit rls =
  camlp4_state := ByGrammar (weaken_entry te,pos,rls,reinit) :: !camlp4_state;
  camlp4_verbosity (Flags.is_verbose ()) (G.extend te pos) rls

(* n is the number of extended entries (not the number of Grammar commands!)
   to remove. *)
let rec remove_grammars n =
  if n>0 then
    (match !camlp4_state with
       | [] -> anomaly "Pcoq.remove_grammars: too many rules to remove"
       | ByGrammar(g,pos,rls,reinit)::t ->
           grammar_delete g pos reinit rls;
           camlp4_state := t;
           remove_grammars (n-1)
       | ByGEXTEND (undo,redo)::t ->
           undo();
           camlp4_state := t;
           remove_grammars n;
           redo();
           camlp4_state := ByGEXTEND (undo,redo) :: !camlp4_state)

(* An entry that checks we reached the end of the input. *)
let eoi_entry en =
  let e = Gram.Entry.create ((Gram.Entry.name en) ^ "_eoi") in
  GEXTEND Gram
    e: [ [ x = en; EOI -> x ] ]
    ;
  END;
  e

let map_entry f en =
  let e = Gram.Entry.create ((Gram.Entry.name en) ^ "_map") in
  GEXTEND Gram
    e: [ [ x = en -> f x ] ]
    ;
  END;
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f x =
  let strm = Stream.of_string x in Gram.Entry.parse f (Gram.parsable strm)

type gram_universe = string * (string, typed_entry) Hashtbl.t

let trace = ref false

(* The univ_tab is not part of the state. It contains all the grammars that
   exist or have existed before in the session. *)

let univ_tab = (Hashtbl.create 7 : (string, gram_universe) Hashtbl.t)

let create_univ s =
  let u = s, Hashtbl.create 29 in Hashtbl.add univ_tab s u; u

let uprim   = create_univ "prim"
let uconstr = create_univ "constr"
let utactic = create_univ "tactic"
let uvernac = create_univ "vernac"

let get_univ s =
  try
    Hashtbl.find univ_tab s
  with Not_found ->
    anomaly ("Unknown grammar universe: "^s)

let get_entry (u, utab) s = Hashtbl.find utab s

let get_entry_type (u, utab) s =
  try
    type_of_typed_entry (get_entry (u, utab) s)
  with Not_found ->
    errorlabstrm "Pcoq.get_entry"
      (str "Unknown grammar entry " ++ str u ++ str ":" ++ str s ++ str ".")

let new_entry etyp (u, utab) s =
  if !trace then (Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr);
  let ename = u ^ ":" ^ s in
  let e = in_typed_entry etyp (Gram.Entry.create ename) in
  Hashtbl.add utab s e; e

let create_entry (u, utab) s etyp =
  try
    let e = Hashtbl.find utab s in
    if type_of_typed_entry e <> etyp then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type");
    e
  with Not_found ->
    new_entry etyp (u, utab) s

let create_constr_entry s =
  outGramObj rawwit_constr (create_entry uconstr s ConstrArgType)

let create_generic_entry s wit =
  outGramObj wit (create_entry utactic s (unquote wit))

(* [make_gen_entry] builds entries extensible by giving its name (a string) *)
(* For entries extensible only via the ML name, Gram.Entry.create is enough *)

let make_gen_entry (u,univ) rawwit s =
  let e = Gram.Entry.create (u ^ ":" ^ s) in
  Hashtbl.add univ s (inGramObj rawwit e); e

(* Initial grammar entries *)

module Prim =
  struct
    let gec_gen x = make_gen_entry uprim x

    (* Entries that can be refered via the string -> Gram.Entry.e table *)
    (* Typically for tactic or vernac extensions *)
    let preident = gec_gen rawwit_pre_ident "preident"
    let ident = gec_gen rawwit_ident "ident"
    let natural = gec_gen rawwit_int "natural"
    let integer = gec_gen rawwit_int "integer"
    let bigint = Gram.Entry.create "Prim.bigint"
    let string = gec_gen rawwit_string "string"
    let reference = make_gen_entry uprim rawwit_ref "reference"
    let by_notation = Gram.Entry.create "by_notation"
    let smart_global = Gram.Entry.create "smart_global"

    (* parsed like ident but interpreted as a term *)
    let var = gec_gen rawwit_var "var"

    let name = Gram.Entry.create "Prim.name"
    let identref = Gram.Entry.create "Prim.identref"
    let pattern_ident = gec_gen rawwit_pattern_ident "pattern_ident"
    let pattern_identref = Gram.Entry.create "pattern_identref"

    (* A synonym of ident - maybe ident will be located one day *)
    let base_ident = Gram.Entry.create "Prim.base_ident"

    let qualid = Gram.Entry.create "Prim.qualid"
    let fullyqualid = Gram.Entry.create "Prim.fullyqualid"
    let dirpath = Gram.Entry.create "Prim.dirpath"

    let ne_string = Gram.Entry.create "Prim.ne_string"
    let ne_lstring = Gram.Entry.create "Prim.ne_lstring"

  end

module Constr =
  struct
    let gec_constr = make_gen_entry uconstr rawwit_constr
    let gec_constr_list = make_gen_entry uconstr (wit_list0 rawwit_constr)

    (* Entries that can be refered via the string -> Gram.Entry.e table *)
    let constr = gec_constr "constr"
    let operconstr = gec_constr "operconstr"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let binder_constr = create_constr_entry "binder_constr"
    let ident = make_gen_entry uconstr rawwit_ident "ident"
    let global = make_gen_entry uconstr rawwit_ref "global"
    let sort = make_gen_entry uconstr rawwit_sort "sort"
    let pattern = Gram.Entry.create "constr:pattern"
    let constr_pattern = gec_constr "constr_pattern"
    let lconstr_pattern = gec_constr "lconstr_pattern"
    let binder = Gram.Entry.create "constr:binder"
    let binder_let = Gram.Entry.create "constr:binder_let"
    let binders_let = Gram.Entry.create "constr:binders_let"
    let binders_let_fixannot = Gram.Entry.create "constr:binders_let_fixannot"
    let typeclass_constraint = Gram.Entry.create "constr:typeclass_constraint"
    let record_declaration = Gram.Entry.create "constr:record_declaration"
    let appl_arg = Gram.Entry.create "constr:appl_arg"
  end

module Module =
  struct
    let module_expr = Gram.Entry.create "module_expr"
    let module_type = Gram.Entry.create "module_type"
  end

module Tactic =
  struct
    (* Main entry for extensions *)
    let simple_tactic = Gram.Entry.create "tactic:simple_tactic"

    (* Entries that can be refered via the string -> Gram.Entry.e table *)
    (* Typically for tactic user extensions *)
    let open_constr =
      make_gen_entry utactic (rawwit_open_constr_gen false) "open_constr"
    let casted_open_constr =
      make_gen_entry utactic (rawwit_open_constr_gen true) "casted_open_constr"
    let constr_with_bindings =
      make_gen_entry utactic rawwit_constr_with_bindings "constr_with_bindings"
    let bindings =
      make_gen_entry utactic rawwit_bindings "bindings"
    let constr_may_eval = make_gen_entry utactic rawwit_constr_may_eval "constr_may_eval"
    let quantified_hypothesis =
      make_gen_entry utactic rawwit_quant_hyp "quantified_hypothesis"
    let int_or_var = make_gen_entry utactic rawwit_int_or_var "int_or_var"
    let red_expr = make_gen_entry utactic rawwit_red_expr "red_expr"
    let simple_intropattern =
      make_gen_entry utactic rawwit_intro_pattern "simple_intropattern"

    (* Main entries for ltac *)
    let tactic_arg = Gram.Entry.create "tactic:tactic_arg"
    let tactic_expr = Gram.Entry.create "tactic:tactic_expr"
    let binder_tactic = Gram.Entry.create "tactic:binder_tactic"

    let tactic = make_gen_entry utactic (rawwit_tactic tactic_main_level) "tactic"

    (* Main entry for quotations *)
    let tactic_eoi = eoi_entry tactic

  end

module Vernac_ =
  struct
    let gec_vernac s = Gram.Entry.create ("vernac:" ^ s)

    (* The different kinds of vernacular commands *)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac = gec_vernac "Vernac.vernac"
    let proof_instr = Gram.Entry.create "proofmode:instr"

    let vernac_eoi = eoi_entry vernac

    (* Main vernac entry *)
    let main_entry = Gram.Entry.create "vernac"
    GEXTEND Gram
    main_entry:
      [ [ a = vernac -> Some (loc,a) | EOI -> None ] ]
    ;
    END

  end

let main_entry = Vernac_.main_entry

(**********************************************************************)
(* This determines (depending on the associativity of the current
   level and on the expected associativity) if a reference to constr_n is
   a reference to the current level (to be translated into "SELF" on the
   left border and into "constr LEVEL n" elsewhere), to the level below
   (to be translated into "NEXT") or to an below wrt associativity (to be
   translated in camlp4 into "constr" without level) or to another level
   (to be translated into "constr LEVEL n")

   The boolean is true if the entry was existing _and_ empty; this to
   circumvent a weakness of camlp4/camlp5 whose undo mechanism is not the
   converse of the extension mechanism *)

let constr_level = string_of_int

let default_levels =
  [200,Gramext.RightA,false;
   100,Gramext.RightA,false;
   99,Gramext.RightA,true;
   90,Gramext.RightA,false;
   10,Gramext.RightA,false;
   9,Gramext.RightA,false;
   8,Gramext.RightA,true;
   1,Gramext.LeftA,false;
   0,Gramext.RightA,false]

let default_pattern_levels =
  [200,Gramext.RightA,true;
   100,Gramext.RightA,false;
   99,Gramext.RightA,true;
   10,Gramext.LeftA,false;
   1,Gramext.LeftA,false;
   0,Gramext.RightA,false]

let level_stack =
  ref [(default_levels, default_pattern_levels)]

(* At a same level, LeftA takes precedence over RightA and NoneA *)
(* In case, several associativity exists for a level, we make two levels, *)
(* first LeftA, then RightA and NoneA together *)
open Ppextend

let admissible_assoc = function
  | Gramext.LeftA, Some (Gramext.RightA | Gramext.NonA) -> false
  | Gramext.RightA, Some Gramext.LeftA -> false
  | _ -> true

let create_assoc = function
  | None -> Gramext.RightA
  | Some a -> a

let error_level_assoc p current expected =
  let pr_assoc = function
    | Gramext.LeftA -> str "left"
    | Gramext.RightA -> str "right"
    | Gramext.NonA -> str "non" in
  errorlabstrm ""
    (str "Level " ++ int p ++ str " is already declared " ++
     pr_assoc current ++ str " associative while it is now expected to be " ++
     pr_assoc expected ++ str " associative.")

let find_position_gen forpat ensure assoc lev =
  let ccurrent,pcurrent as current = List.hd !level_stack in
  match lev with
  | None ->
      level_stack := current :: !level_stack;
      None, None, None, None
  | Some n ->
      let after = ref None in
      let init = ref None in
      let rec add_level q = function
        | (p,_,_ as pa)::l when p > n -> pa :: add_level (Some p) l
        | (p,a,reinit)::l when p = n ->
            if reinit then
	      let a' = create_assoc assoc in (init := Some a'; (p,a',false)::l)
	    else if admissible_assoc (a,assoc) then
	      raise Exit
            else
	      error_level_assoc p a (Option.get assoc)
	| l -> after := q; (n,create_assoc assoc,ensure)::l
      in
      try
	let updated =
	  if forpat then (ccurrent, add_level None pcurrent)
	  else (add_level None ccurrent, pcurrent) in
        level_stack := updated:: !level_stack;
	let assoc = create_assoc assoc in
        if !init = None then
	  (* Create the entry *)
	  (if !after = None then Some Gramext.First
	   else Some (Gramext.After (constr_level (Option.get !after)))),
	   Some assoc, Some (constr_level n), None
        else
	  (* The reinit flag has been updated *)
	   Some (Gramext.Level (constr_level n)), None, None, !init
      with
	  (* Nothing has changed *)
          Exit ->
            level_stack := current :: !level_stack;
	    (* Just inherit the existing associativity and name (None) *)
	    Some (Gramext.Level (constr_level n)), None, None, None

let remove_levels n =
  level_stack := list_skipn n !level_stack

let rec list_mem_assoc_triple x = function
  | [] -> false
  | (a,b,c) :: l -> a = x or list_mem_assoc_triple x l

let register_empty_levels forpat levels =
  map_succeed (fun n ->
    let levels = (if forpat then snd else fst) (List.hd !level_stack) in
    if not (list_mem_assoc_triple n levels) then
      find_position_gen forpat true None (Some n)
    else
      failwith "") levels

let find_position forpat assoc level =
  find_position_gen forpat false assoc level

(* Synchronise the stack of level updates *)
let synchronize_level_positions () =
  let _ = find_position true None None in ()

(**********************************************************************)
(* Binding constr entry keys to entries                               *)

(* Camlp4 levels do not treat NonA: use RightA with a NEXT on the left *)
let camlp4_assoc = function
  | Some Gramext.NonA | Some Gramext.RightA -> Gramext.RightA
  | None | Some Gramext.LeftA -> Gramext.LeftA

(* [adjust_level assoc from prod] where [assoc] and [from] are the name
   and associativity of the level where to add the rule; the meaning of
   the result is

     None = SELF
     Some None = NEXT
     Some (Some (n,cur)) = constr LEVEL n
         s.t. if [cur] is set then [n] is the same as the [from] level *)
let adjust_level assoc from = function
(* Associativity is None means force the level *)
  | (NumLevel n,BorderProd (_,None)) -> Some (Some (n,true))
(* Compute production name on the right side *)
  (* If NonA or LeftA on the right-hand side, set to NEXT *)
  | (NumLevel n,BorderProd (Right,Some (Gramext.NonA|Gramext.LeftA))) ->
      Some None
  (* If RightA on the right-hand side, set to the explicit (current) level *)
  | (NumLevel n,BorderProd (Right,Some Gramext.RightA)) ->
      Some (Some (n,true))
(* Compute production name on the left side *)
  (* If NonA on the left-hand side, adopt the current assoc ?? *)
  | (NumLevel n,BorderProd (Left,Some Gramext.NonA)) -> None
  (* If the expected assoc is the current one, set to SELF *)
  | (NumLevel n,BorderProd (Left,Some a)) when a = camlp4_assoc assoc ->
      None
  (* Otherwise, force the level, n or n-1, according to expected assoc *)
  | (NumLevel n,BorderProd (Left,Some a)) ->
      if a = Gramext.LeftA then Some (Some (n,true)) else Some None
  (* None means NEXT *)
  | (NextLevel,_) -> Some None
(* Compute production name elsewhere *)
  | (NumLevel n,InternalProd) ->
      match from with
	| ETConstr (p,()) when p = n+1 -> Some None
	| ETConstr (p,()) -> Some (Some (n,n=p))
	| _ -> Some (Some (n,false))

let compute_entry allow_create adjust forpat = function
  | ETConstr (n,q) ->
      (if forpat then weaken_entry Constr.pattern
       else weaken_entry Constr.operconstr),
      adjust (n,q), false
  | ETName -> weaken_entry Prim.name, None, false
  | ETBigint -> weaken_entry Prim.bigint, None, false
  | ETReference -> weaken_entry Constr.global, None, false
  | ETPattern -> weaken_entry Constr.pattern, None, false
  | ETConstrList _ -> error "List of entries cannot be registered."
  | ETOther (u,n) ->
      let u = get_univ u in
      let e =
        try get_entry u n
        with Not_found when allow_create -> create_entry u n ConstrArgType in
      object_of_typed_entry e, None, true

(* This computes the name of the level where to add a new rule *)
let interp_constr_entry_key forpat = function
  | ETConstr(200,()) when not forpat ->
      weaken_entry Constr.binder_constr, None
  | e ->
      let (e,level,_) = compute_entry true (fun (n,()) -> Some n) forpat e in
      (e, level)

(* This computes the name to give to a production knowing the name and
   associativity of the level where it must be added *)
let interp_constr_prod_entry_key ass from forpat en =
  compute_entry false (adjust_level ass from) forpat en

(**********************************************************************)
(* Binding constr entry keys to symbols                               *)

let is_self from e =
  match from, e with
      ETConstr(n,()), ETConstr(NumLevel n',
        BorderProd(Right, _ (* Some(Gramext.NonA|Gramext.LeftA) *))) -> false
    | ETConstr(n,()), ETConstr(NumLevel n',BorderProd(Left,_)) -> n=n'
    | (ETName,ETName | ETReference, ETReference | ETBigint,ETBigint
      | ETPattern, ETPattern) -> true
    | ETOther(s1,s2), ETOther(s1',s2') -> s1=s1' & s2=s2'
    | _ -> false

let is_binder_level from e =
  match from, e with
      ETConstr(200,()),
      ETConstr(NumLevel 200,(BorderProd(Right,_)|InternalProd)) -> true
    | _ -> false

let rec symbol_of_constr_prod_entry_key assoc from forpat typ =
  if is_binder_level from typ then
    if forpat then
      Gramext.Snterml (Gram.Entry.obj Constr.pattern,"200")
    else
      Gramext.Snterml (Gram.Entry.obj Constr.operconstr,"200")
  else if is_self from typ then
    Gramext.Sself
  else
    match typ with
    | ETConstrList (typ',[]) ->
        Gramext.Slist1 (symbol_of_constr_prod_entry_key assoc from forpat (ETConstr typ'))
    | ETConstrList (typ',tkl) ->
        Gramext.Slist1sep
          (symbol_of_constr_prod_entry_key assoc from forpat (ETConstr typ'),
           Gramext.srules
             [List.map (fun x -> Gramext.Stoken x) tkl,
              List.fold_right (fun _ v -> Gramext.action (fun _ -> v)) tkl
                (Gramext.action (fun loc -> ()))])
    | _ ->
    match interp_constr_prod_entry_key assoc from forpat typ with
      | (eobj,None,_) -> Gramext.Snterm (Gram.Entry.obj eobj)
      | (eobj,Some None,_) -> Gramext.Snext
      | (eobj,Some (Some (lev,cur)),_) ->
          Gramext.Snterml (Gram.Entry.obj eobj,constr_level lev)

(**********************************************************************)
(* Binding general entry keys to symbol                               *)

let rec symbol_of_prod_entry_key = function
  | Alist1 s -> Gramext.Slist1 (symbol_of_prod_entry_key s)
  | Alist1sep (s,sep) ->
      Gramext.Slist1sep (symbol_of_prod_entry_key s, Gramext.Stoken ("",sep))
  | Alist0 s -> Gramext.Slist0 (symbol_of_prod_entry_key s)
  | Alist0sep (s,sep) ->
      Gramext.Slist0sep (symbol_of_prod_entry_key s, Gramext.Stoken ("",sep))
  | Aopt s -> Gramext.Sopt (symbol_of_prod_entry_key s)
  | Amodifiers s ->
       Gramext.srules
        [([], Gramext.action(fun _loc -> []));
         ([Gramext.Stoken ("", "(");
           Gramext.Slist1sep ((symbol_of_prod_entry_key s), Gramext.Stoken ("", ","));
           Gramext.Stoken ("", ")")],
	   Gramext.action (fun _ l _ _loc -> l))]
  | Aself -> Gramext.Sself
  | Anext -> Gramext.Snext
  | Atactic 5 -> Gramext.Snterm (Gram.Entry.obj Tactic.binder_tactic)
  | Atactic n ->
      Gramext.Snterml (Gram.Entry.obj Tactic.tactic_expr, string_of_int n)
  | Agram s -> Gramext.Snterm s
  | Aentry (u,s) ->
      Gramext.Snterm (Gram.Entry.obj
	(object_of_typed_entry (get_entry (get_univ u) s)))

(**********************************************************************)
(* Interpret entry names of the form "ne_constr_list" as entry keys   *)

let rec interp_entry_name static up_level s sep =
  let l = String.length s in
  if l > 8 & String.sub s 0 3 = "ne_" & String.sub s (l-5) 5 = "_list" then
    let t, g = interp_entry_name static up_level (String.sub s 3 (l-8)) "" in
    List1ArgType t, Alist1 g
  else if l > 12 & String.sub s 0 3 = "ne_" &
                   String.sub s (l-9) 9 = "_list_sep" then
    let t, g = interp_entry_name static up_level (String.sub s 3 (l-12)) "" in
    List1ArgType t, Alist1sep (g,sep)
  else if l > 5 & String.sub s (l-5) 5 = "_list" then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-5)) "" in
    List0ArgType t, Alist0 g
  else if l > 9 & String.sub s (l-9) 9 = "_list_sep" then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-9)) "" in
    List0ArgType t, Alist0sep (g,sep)
  else if l > 4 & String.sub s (l-4) 4 = "_opt" then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-4)) "" in
    OptArgType t, Aopt g
  else if l > 5 & String.sub s (l-5) 5 = "_mods" then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-1)) "" in
    List0ArgType t, Amodifiers g
  else
    let s = if s = "hyp" then "var" else s in
    let t, se =
      match Extrawit.tactic_genarg_level s with
	| Some n when Some n = up_level & up_level <> Some 5 -> None, Aself
	| Some n when Some (n+1) = up_level & up_level <> Some 5 -> None, Anext
	| Some n -> None, Atactic n
	| None ->
      try Some (get_entry uprim s), Aentry ("prim",s) with Not_found ->
      try Some (get_entry uconstr s), Aentry ("constr",s) with Not_found ->
      try Some (get_entry utactic s), Aentry ("tactic",s) with Not_found ->
	if static then
	  error ("Unknown entry "^s^".")
	else
	  None, Aentry ("",s) in
    let t =
      match t with
	| Some t -> type_of_typed_entry t
	| None -> ExtraArgType s in
    t, se
