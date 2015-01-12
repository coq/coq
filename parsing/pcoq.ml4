(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Compat
open Errors
open Util
open Extend
open Genarg
open Stdarg
open Constrarg
open Tok (* necessary for camlp4 *)

(** The parser of Coq *)

module G = GrammarMake (Lexer)

(* TODO: this is a workaround, since there isn't such
   [warning_verbose] in new camlp4. In camlp5, this ref
   gets hidden by [Gramext.warning_verbose] *)
let warning_verbose = ref true

IFDEF CAMLP5 THEN
open Gramext
ELSE
open PcamlSig.Grammar
open G
END

(** Compatibility with Camlp5 6.x *)

IFDEF CAMLP5_6_00 THEN
let slist0sep x y = Slist0sep (x, y, false)
let slist1sep x y = Slist1sep (x, y, false)
ELSE
let slist0sep x y = Slist0sep (x, y)
let slist1sep x y = Slist1sep (x, y)
END

let gram_token_of_token tok =
IFDEF CAMLP5 THEN
 Stoken (Tok.to_pattern tok)
ELSE
 match tok with
  | KEYWORD s -> Skeyword s
  | tok -> Stoken ((=) tok, to_string tok)
END

let gram_token_of_string s = gram_token_of_token (Lexer.terminal s)

let camlp4_verbosity silent f x =
  let a = !warning_verbose in
  warning_verbose := silent;
  f x;
  warning_verbose := a

let camlp4_verbose f x = camlp4_verbosity (Flags.is_verbose ()) f x


(** General entry keys *)

(** This intermediate abstract representation of entries can
   both be reified into mlexpr for the ML extensions and
   dynamically interpreted as entries for the Coq level extensions
*)

type prod_entry_key =
  | Alist1 of prod_entry_key
  | Alist1sep of prod_entry_key * string
  | Alist0 of prod_entry_key
  | Alist0sep of prod_entry_key * string
  | Aopt of prod_entry_key
  | Amodifiers of prod_entry_key
  | Aself
  | Anext
  | Atactic of int
  | Agram of string
  | Aentry of string * string

(** [grammar_object] is the superclass of all grammar entries *)

module type Gramobj =
sig
  type grammar_object
  val weaken_entry : 'a G.entry -> grammar_object G.entry
end

module Gramobj : Gramobj =
struct
  type grammar_object = Obj.t
  let weaken_entry e = Obj.magic e
end

(** Grammar entries with associated types *)

type entry_type = argument_type
type grammar_object = Gramobj.grammar_object
type typed_entry = argument_type * grammar_object G.entry
let in_typed_entry t e = (t,Gramobj.weaken_entry e)
let type_of_typed_entry (t,e) = t
let object_of_typed_entry (t,e) = e
let weaken_entry x = Gramobj.weaken_entry x

module type Gramtypes =
sig
  val inGramObj : 'a raw_abstract_argument_type -> 'a G.entry -> typed_entry
  val outGramObj : 'a raw_abstract_argument_type -> typed_entry -> 'a G.entry
end

module Gramtypes : Gramtypes =
struct
  let inGramObj rawwit = in_typed_entry (unquote rawwit)
  let outGramObj (a:'a raw_abstract_argument_type) o =
    if not (argument_type_eq (type_of_typed_entry o) (unquote a))
      then anomaly ~label:"outGramObj" (str "wrong type");
    (* downcast from grammar_object *)
    Obj.magic (object_of_typed_entry o)
end

open Gramtypes

(** Grammar extensions *)

(** NB: [extend_statment =
         gram_position option * single_extend_statment list]
    and [single_extend_statment =
         string option * gram_assoc option * production_rule list]
    and [production_rule = symbol list * action]

    In [single_extend_statement], first two parameters are name and
    assoc iff a level is created *)

(** Type of reinitialization data *)
type gram_reinit = gram_assoc * gram_position

type ext_kind =
  | ByGrammar of
      grammar_object G.entry
      * gram_reinit option (** for reinitialization if ever needed *)
      * G.extend_statment
  | ByEXTEND of (unit -> unit) * (unit -> unit)

(** The list of extensions *)

let camlp4_state = ref []

(** Deletion *)

let grammar_delete e reinit (pos,rls) =
  List.iter
    (fun (n,ass,lev) ->
      List.iter (fun (pil,_) -> G.delete_rule e pil) (List.rev lev))
    (List.rev rls);
  match reinit with
  | Some (a,ext) ->
    let lev = match pos with Some (Level n) -> n | _ -> assert false in
    maybe_uncurry (G.extend e) (Some ext, [Some lev,Some a,[]])
  | None -> ()

(** The apparent parser of Coq; encapsulate G to keep track
    of the extensions. *)

module Gram =
  struct
    include G
    let extend e =
      maybe_curry
	(fun ext ->
	   camlp4_state :=
	     (ByEXTEND ((fun () -> grammar_delete e None ext),
			(fun () -> maybe_uncurry (G.extend e) ext)))
	   :: !camlp4_state;
	   maybe_uncurry (G.extend e) ext)
    let delete_rule e pil =
      (* spiwack: if you use load an ML module which contains GDELETE_RULE
	  in a section, God kills a kitty. As it would corrupt remove_grammars.
          There does not seem to be a good way to undo a delete rule. As deleting
	  takes fewer arguments than extending. The production rule isn't returned
	  by delete_rule. If we could retrieve the necessary information, then
	  ByEXTEND provides just the framework we need to allow this in section.
	  I'm not entirely sure it makes sense, but at least it would be more correct.
          *)
      G.delete_rule e pil
  end

(** This extension command is used by the Grammar constr *)

let grammar_extend e reinit ext =
  camlp4_state := ByGrammar (weaken_entry e,reinit,ext) :: !camlp4_state;
  camlp4_verbose (maybe_uncurry (G.extend e)) ext

(** Remove extensions

   [n] is the number of extended entries (not the number of Grammar commands!)
   to remove. *)

let rec remove_grammars n =
  if n>0 then
    (match !camlp4_state with
       | [] -> anomaly ~label:"Pcoq.remove_grammars" (Pp.str "too many rules to remove")
       | ByGrammar(g,reinit,ext)::t ->
           let f (a,b) = (of_coq_assoc a, of_coq_position b) in
           grammar_delete g (Option.map f reinit) ext;
           camlp4_state := t;
           remove_grammars (n-1)
       | ByEXTEND (undo,redo)::t ->
           undo();
           camlp4_state := t;
           remove_grammars n;
           redo();
           camlp4_state := ByEXTEND (undo,redo) :: !camlp4_state)

(** An entry that checks we reached the end of the input. *)

let eoi_entry en =
  let e = Gram.entry_create ((Gram.Entry.name en) ^ "_eoi") in
  GEXTEND Gram
    e: [ [ x = en; EOI -> x ] ]
    ;
  END;
  e

let map_entry f en =
  let e = Gram.entry_create ((Gram.Entry.name en) ^ "_map") in
  GEXTEND Gram
    e: [ [ x = en -> f x ] ]
    ;
  END;
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f x =
  let strm = Stream.of_string x in Gram.entry_parse f (Gram.parsable strm)

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
    anomaly (Pp.str ("Unknown grammar universe: "^s))

let get_entry (u, utab) s = Hashtbl.find utab s

let new_entry etyp (u, utab) s =
  if !trace then (Printf.eprintf "[Creating entry %s:%s]\n" u s; flush stderr);
  let ename = u ^ ":" ^ s in
  let e = in_typed_entry etyp (Gram.entry_create ename) in
  Hashtbl.add utab s e; e

let create_entry (u, utab) s etyp =
  try
    let e = Hashtbl.find utab s in
    if not (argument_type_eq (type_of_typed_entry e) etyp) then
      failwith ("Entry " ^ u ^ ":" ^ s ^ " already exists with another type");
    e
  with Not_found ->
    new_entry etyp (u, utab) s

let create_constr_entry s =
  outGramObj (rawwit wit_constr) (create_entry uconstr s ConstrArgType)

let create_generic_entry s wit =
  outGramObj wit (create_entry utactic s (unquote wit))

(* [make_gen_entry] builds entries extensible by giving its name (a string) *)
(* For entries extensible only via the ML name, Gram.entry_create is enough *)

let make_gen_entry (u,univ) rawwit s =
  let e = Gram.entry_create (u ^ ":" ^ s) in
  Hashtbl.add univ s (inGramObj rawwit e); e

(* Initial grammar entries *)

module Prim =
  struct
    let gec_gen x = make_gen_entry uprim x

    (* Entries that can be refered via the string -> Gram.entry table *)
    (* Typically for tactic or vernac extensions *)
    let preident = gec_gen (rawwit wit_pre_ident) "preident"
    let ident = gec_gen (rawwit wit_ident) "ident"
    let natural = gec_gen (rawwit wit_int) "natural"
    let integer = gec_gen (rawwit wit_int) "integer"
    let bigint = Gram.entry_create "Prim.bigint"
    let string = gec_gen (rawwit wit_string) "string"
    let reference = make_gen_entry uprim (rawwit wit_ref) "reference"
    let by_notation = Gram.entry_create "by_notation"
    let smart_global = Gram.entry_create "smart_global"

    (* parsed like ident but interpreted as a term *)
    let var = gec_gen (rawwit wit_var) "var"

    let name = Gram.entry_create "Prim.name"
    let identref = Gram.entry_create "Prim.identref"
    let pattern_ident = Gram.entry_create "pattern_ident"
    let pattern_identref = Gram.entry_create "pattern_identref"

    (* A synonym of ident - maybe ident will be located one day *)
    let base_ident = Gram.entry_create "Prim.base_ident"

    let qualid = Gram.entry_create "Prim.qualid"
    let fullyqualid = Gram.entry_create "Prim.fullyqualid"
    let dirpath = Gram.entry_create "Prim.dirpath"

    let ne_string = Gram.entry_create "Prim.ne_string"
    let ne_lstring = Gram.entry_create "Prim.ne_lstring"

  end

module Constr =
  struct
    let gec_constr = make_gen_entry uconstr (rawwit wit_constr)

    (* Entries that can be refered via the string -> Gram.entry table *)
    let constr = gec_constr "constr"
    let operconstr = gec_constr "operconstr"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let binder_constr = create_constr_entry "binder_constr"
    let ident = make_gen_entry uconstr (rawwit wit_ident) "ident"
    let global = make_gen_entry uconstr (rawwit wit_ref) "global"
    let sort = make_gen_entry uconstr (rawwit wit_sort) "sort"
    let pattern = Gram.entry_create "constr:pattern"
    let constr_pattern = gec_constr "constr_pattern"
    let lconstr_pattern = gec_constr "lconstr_pattern"
    let closed_binder = Gram.entry_create "constr:closed_binder"
    let binder = Gram.entry_create "constr:binder"
    let binders = Gram.entry_create "constr:binders"
    let open_binders = Gram.entry_create "constr:open_binders"
    let binders_fixannot = Gram.entry_create "constr:binders_fixannot"
    let typeclass_constraint = Gram.entry_create "constr:typeclass_constraint"
    let record_declaration = Gram.entry_create "constr:record_declaration"
    let appl_arg = Gram.entry_create "constr:appl_arg"
  end

module Module =
  struct
    let module_expr = Gram.entry_create "module_expr"
    let module_type = Gram.entry_create "module_type"
  end

module Tactic =
  struct
    (* Main entry for extensions *)
    let simple_tactic = Gram.entry_create "tactic:simple_tactic"

    (* Entries that can be refered via the string -> Gram.entry table *)
    (* Typically for tactic user extensions *)
    let open_constr =
      make_gen_entry utactic (rawwit wit_open_constr) "open_constr"
    let constr_with_bindings =
      make_gen_entry utactic (rawwit wit_constr_with_bindings) "constr_with_bindings"
    let bindings =
      make_gen_entry utactic (rawwit wit_bindings) "bindings"
    let constr_may_eval = make_gen_entry utactic (rawwit wit_constr_may_eval) "constr_may_eval"
    let uconstr =
      make_gen_entry utactic (rawwit wit_uconstr) "uconstr"
    let quantified_hypothesis =
      make_gen_entry utactic (rawwit wit_quant_hyp) "quantified_hypothesis"
    let int_or_var = make_gen_entry utactic (rawwit wit_int_or_var) "int_or_var"
    let red_expr = make_gen_entry utactic (rawwit wit_red_expr) "red_expr"
    let simple_intropattern =
      make_gen_entry utactic (rawwit wit_intro_pattern) "simple_intropattern"
    let clause_dft_concl = 
      make_gen_entry utactic (rawwit wit_clause_dft_concl) "clause"


    (* Main entries for ltac *)
    let tactic_arg = Gram.entry_create "tactic:tactic_arg"
    let tactic_expr = Gram.entry_create "tactic:tactic_expr"
    let binder_tactic = Gram.entry_create "tactic:binder_tactic"

    let tactic = make_gen_entry utactic (rawwit wit_tactic) "tactic"

    (* Main entry for quotations *)
    let tactic_eoi = eoi_entry tactic

    (* For Ltac definition *)
    let tacdef_body = Gram.entry_create "tactic:tacdef_body"

  end

module Vernac_ =
  struct
    let gec_vernac s = Gram.entry_create ("vernac:" ^ s)

    (* The different kinds of vernacular commands *)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac = gec_vernac "Vernac.vernac"
    let vernac_eoi = eoi_entry vernac
    let rec_definition = gec_vernac "Vernac.rec_definition"
    (* Main vernac entry *)
    let main_entry = Gram.entry_create "vernac"

    GEXTEND Gram
    main_entry:
      [ [ a = vernac -> Some (!@loc, a) | EOI -> None ] ]
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
  [200,Extend.RightA,false;
   100,Extend.RightA,false;
   99,Extend.RightA,true;
   10,Extend.RightA,false;
   9,Extend.RightA,false;
   8,Extend.RightA,true;
   1,Extend.LeftA,false;
   0,Extend.RightA,false]

let default_pattern_levels =
  [200,Extend.RightA,true;
   100,Extend.RightA,false;
   99,Extend.RightA,true;
   10,Extend.LeftA,false;
   9,Extend.RightA,false;
   1,Extend.LeftA,false;
   0,Extend.RightA,false]

let level_stack =
  ref [(default_levels, default_pattern_levels)]

(* At a same level, LeftA takes precedence over RightA and NoneA *)
(* In case, several associativity exists for a level, we make two levels, *)
(* first LeftA, then RightA and NoneA together *)

let admissible_assoc = function
  | Extend.LeftA, Some (Extend.RightA | Extend.NonA) -> false
  | Extend.RightA, Some Extend.LeftA -> false
  | _ -> true

let create_assoc = function
  | None -> Extend.RightA
  | Some a -> a

let error_level_assoc p current expected =
  let pr_assoc = function
    | Extend.LeftA -> str "left"
    | Extend.RightA -> str "right"
    | Extend.NonA -> str "non" in
  errorlabstrm ""
    (str "Level " ++ int p ++ str " is already declared " ++
     pr_assoc current ++ str " associative while it is now expected to be " ++
     pr_assoc expected ++ str " associative.")

let create_pos = function
  | None -> Extend.First
  | Some lev -> Extend.After (constr_level lev)

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
        | (p,a,reinit)::l when Int.equal p n ->
            if reinit then
	      let a' = create_assoc assoc in
              (init := Some (a',create_pos q); (p,a',false)::l)
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
        begin match !init with
        | None ->
	  (* Create the entry *)
	   Some (create_pos !after), Some assoc, Some (constr_level n), None
        | _ ->
	  (* The reinit flag has been updated *)
	   Some (Extend.Level (constr_level n)), None, None, !init
        end
      with
	  (* Nothing has changed *)
          Exit ->
            level_stack := current :: !level_stack;
	    (* Just inherit the existing associativity and name (None) *)
	    Some (Extend.Level (constr_level n)), None, None, None

let remove_levels n =
  level_stack := List.skipn n !level_stack

let rec list_mem_assoc_triple x = function
  | [] -> false
  | (a,b,c) :: l -> Int.equal a x || list_mem_assoc_triple x l

let register_empty_levels forpat levels =
  let filter n =
    try
      let levels = (if forpat then snd else fst) (List.hd !level_stack) in
      if not (list_mem_assoc_triple n levels) then
        Some (find_position_gen forpat true None (Some n))
      else None
    with Failure _ -> None
  in
  List.map_filter filter levels

let find_position forpat assoc level =
  find_position_gen forpat false assoc level

(* Synchronise the stack of level updates *)
let synchronize_level_positions () =
  let _ = find_position true None None in ()

(**********************************************************************)
(* Binding constr entry keys to entries                               *)

(* Camlp4 levels do not treat NonA: use RightA with a NEXT on the left *)
let camlp4_assoc = function
  | Some Extend.NonA | Some Extend.RightA -> Extend.RightA
  | None | Some Extend.LeftA -> Extend.LeftA

let assoc_eq al ar = match al, ar with
| Extend.NonA, Extend.NonA
| Extend.RightA, Extend.RightA
| Extend.LeftA, Extend.LeftA -> true
| _, _ -> false

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
  | (NumLevel n,BorderProd (Right,Some (Extend.NonA|Extend.LeftA))) ->
      Some None
  (* If RightA on the right-hand side, set to the explicit (current) level *)
  | (NumLevel n,BorderProd (Right,Some Extend.RightA)) ->
      Some (Some (n,true))
(* Compute production name on the left side *)
  (* If NonA on the left-hand side, adopt the current assoc ?? *)
  | (NumLevel n,BorderProd (Left,Some Extend.NonA)) -> None
  (* If the expected assoc is the current one, set to SELF *)
  | (NumLevel n,BorderProd (Left,Some a)) when assoc_eq a (camlp4_assoc assoc) ->
      None
  (* Otherwise, force the level, n or n-1, according to expected assoc *)
  | (NumLevel n,BorderProd (Left,Some a)) ->
    begin match a with
    | Extend.LeftA -> Some (Some (n, true))
    | _ -> Some None
    end
  (* None means NEXT *)
  | (NextLevel,_) -> Some None
(* Compute production name elsewhere *)
  | (NumLevel n,InternalProd) ->
      match from with
	| ETConstr (p,()) when Int.equal p (n + 1) -> Some None
	| ETConstr (p,()) -> Some (Some (n, Int.equal n p))
	| _ -> Some (Some (n,false))

let compute_entry allow_create adjust forpat = function
  | ETConstr (n,q) ->
      (if forpat then weaken_entry Constr.pattern
       else weaken_entry Constr.operconstr),
      adjust (n,q), false
  | ETName -> weaken_entry Prim.name, None, false
  | ETBinder true -> anomaly (Pp.str "Should occur only as part of BinderList")
  | ETBinder false -> weaken_entry Constr.binder, None, false
  | ETBinderList (true,tkl) ->
    let () = match tkl with [] -> () | _ -> assert false in
    weaken_entry Constr.open_binders, None, false
  | ETBinderList (false,_) -> anomaly (Pp.str "List of entries cannot be registered.")
  | ETBigint -> weaken_entry Prim.bigint, None, false
  | ETReference -> weaken_entry Constr.global, None, false
  | ETPattern -> weaken_entry Constr.pattern, None, false
  | ETConstrList _ -> anomaly (Pp.str "List of entries cannot be registered.")
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
        BorderProd(Right, _ (* Some(NonA|LeftA) *))) -> false
    | ETConstr(n,()), ETConstr(NumLevel n',BorderProd(Left,_)) -> Int.equal n n'
    | (ETName,ETName | ETReference, ETReference | ETBigint,ETBigint
      | ETPattern, ETPattern) -> true
    | ETOther(s1,s2), ETOther(s1',s2') ->
      String.equal s1 s1' && String.equal s2 s2'
    | _ -> false

let is_binder_level from e =
  match from, e with
      ETConstr(200,()),
      ETConstr(NumLevel 200,(BorderProd(Right,_)|InternalProd)) -> true
    | _ -> false

let make_sep_rules tkl =
  Gram.srules'
    [List.map gram_token_of_token tkl,
     List.fold_right (fun _ v -> Gram.action (fun _ -> v)) tkl
       (Gram.action (fun loc -> ()))]

let rec symbol_of_constr_prod_entry_key assoc from forpat typ =
  if is_binder_level from typ then
    if forpat then
      Snterml (Gram.Entry.obj Constr.pattern,"200")
    else
      Snterml (Gram.Entry.obj Constr.operconstr,"200")
  else if is_self from typ then
      Sself
  else
    match typ with
    | ETConstrList (typ',[]) ->
        Slist1 (symbol_of_constr_prod_entry_key assoc from forpat (ETConstr typ'))
    | ETConstrList (typ',tkl) ->
        slist1sep
          (symbol_of_constr_prod_entry_key assoc from forpat (ETConstr typ'))
          (make_sep_rules tkl)
    | ETBinderList (false,[]) ->
        Slist1
	  (symbol_of_constr_prod_entry_key assoc from forpat (ETBinder false))
    | ETBinderList (false,tkl) ->
        slist1sep
          (symbol_of_constr_prod_entry_key assoc from forpat (ETBinder false))
          (make_sep_rules tkl)

    | _ ->
    match interp_constr_prod_entry_key assoc from forpat typ with
      | (eobj,None,_) -> Snterm (Gram.Entry.obj eobj)
      | (eobj,Some None,_) -> Snext
      | (eobj,Some (Some (lev,cur)),_) ->
          Snterml (Gram.Entry.obj eobj,constr_level lev)

(** Binding general entry keys to symbol *)

let rec symbol_of_prod_entry_key = function
  | Alist1 s -> Slist1 (symbol_of_prod_entry_key s)
  | Alist1sep (s,sep) ->
      slist1sep (symbol_of_prod_entry_key s) (gram_token_of_string sep)
  | Alist0 s -> Slist0 (symbol_of_prod_entry_key s)
  | Alist0sep (s,sep) ->
      slist0sep (symbol_of_prod_entry_key s) (gram_token_of_string sep)
  | Aopt s -> Sopt (symbol_of_prod_entry_key s)
  | Amodifiers s ->
       Gram.srules'
        [([], Gram.action (fun _loc -> []));
         ([gram_token_of_string "(";
           slist1sep (symbol_of_prod_entry_key s) (gram_token_of_string ",");
           gram_token_of_string ")"],
	   Gram.action (fun _ l _ _loc -> l))]
  | Aself -> Sself
  | Anext -> Snext
  | Atactic 5 -> Snterm (Gram.Entry.obj Tactic.binder_tactic)
  | Atactic n ->
      Snterml (Gram.Entry.obj Tactic.tactic_expr, string_of_int n)
  | Agram s ->
    let e =
      try
      (** ppedrot: we should always generate Agram entries which have already
          been registered, so this should not fail. *)
        let (u, s) = match String.split ':' s with
        | u :: s :: [] -> (u, s)
        | _ -> raise Not_found
        in
        get_entry (get_univ u) s
      with Not_found ->
        Errors.anomaly (str "Unregistered grammar entry: " ++ str s)
    in
    Snterm (Gram.Entry.obj (object_of_typed_entry e))
  | Aentry (u,s) ->
    let e = get_entry (get_univ u) s in
    Snterm (Gram.Entry.obj (object_of_typed_entry e))

let level_of_snterml = function
  | Snterml (_,l) -> int_of_string l
  | _ -> failwith "level_of_snterml"

(**********************************************************************)
(* Interpret entry names of the form "ne_constr_list" as entry keys   *)

let coincide s pat off =
  let len = String.length pat in
  let break = ref true in
  let i = ref 0 in
  while !break && !i < len do
    let c = Char.code s.[off + !i] in
    let d = Char.code pat.[!i] in
    break := Int.equal c d;
    incr i
  done;
  !break

let tactic_level s =
  if Int.equal (String.length s) 7 && coincide s "tactic" 0 then
    let c = s.[6] in if '5' >= c && c >= '0' then Some (Char.code c - 48)
    else None
  else None

let type_of_entry u s =
  type_of_typed_entry (get_entry u s)

let rec interp_entry_name static up_level s sep =
  let l = String.length s in
  if l > 8 && coincide s "ne_" 0 && coincide s "_list" (l - 5) then
    let t, g = interp_entry_name static up_level (String.sub s 3 (l-8)) "" in
    ListArgType t, Alist1 g
  else if l > 12 && coincide s "ne_" 0 &&
                   coincide s "_list_sep" (l-9) then
    let t, g = interp_entry_name static up_level (String.sub s 3 (l-12)) "" in
    ListArgType t, Alist1sep (g,sep)
  else if l > 5 && coincide s "_list" (l-5) then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-5)) "" in
    ListArgType t, Alist0 g
  else if l > 9 && coincide s "_list_sep" (l-9) then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-9)) "" in
    ListArgType t, Alist0sep (g,sep)
  else if l > 4 && coincide s "_opt" (l-4) then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-4)) "" in
    OptArgType t, Aopt g
  else if l > 5 && coincide s "_mods" (l-5) then
    let t, g = interp_entry_name static up_level (String.sub s 0 (l-1)) "" in
    ListArgType t, Amodifiers g
  else
    let s = match s with "hyp" -> "var" | _ -> s in
    let check_lvl n = match up_level with
    | None -> false
    | Some m -> Int.equal m n
                && not (Int.equal m 5) (* Because tactic5 is at binder_tactic *)
                && not (Int.equal m 0) (* Because tactic0 is at simple_tactic *)
    in
    let t, se =
      match tactic_level s with
      | Some n ->
        (** Quite ad-hoc *)
        let t = unquote (rawwit wit_tactic) in
        let se =
          if check_lvl n then Aself
          else if check_lvl (n + 1) then Anext
          else Atactic n
        in
        (Some t, se)
      | None ->
      try Some (type_of_entry uprim s), Aentry ("prim",s) with Not_found ->
      try Some (type_of_entry uconstr s), Aentry ("constr",s) with Not_found ->
      try Some (type_of_entry utactic s), Aentry ("tactic",s) with Not_found ->
	if static then
	  error ("Unknown entry "^s^".")
	else
	  None, Aentry ("",s) in
    let t =
      match t with
	| Some t -> t
	| None -> ExtraArgType s in
    t, se

let list_entry_names () =
  let add_entry key (entry, _) accu = (key, entry) :: accu in
  let ans = Hashtbl.fold add_entry (snd uprim) [] in
  let ans = Hashtbl.fold add_entry (snd uconstr) ans in
  Hashtbl.fold add_entry (snd utactic) ans
