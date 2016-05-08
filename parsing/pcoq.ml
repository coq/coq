(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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

(** The parser of Coq *)

module G = GrammarMake (Lexer)

let warning_verbose = Compat.warning_verbose

module Symbols = GramextMake(G)

let gram_token_of_token = Symbols.stoken
let gram_token_of_string s = gram_token_of_token (Lexer.terminal s)

let camlp4_verbosity silent f x =
  let a = !warning_verbose in
  warning_verbose := silent;
  f x;
  warning_verbose := a

let camlp4_verbose f x = camlp4_verbosity (Flags.is_verbose ()) f x


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

type grammar_object = Gramobj.grammar_object
let weaken_entry x = Gramobj.weaken_entry x

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
    let lev = match Option.map Compat.to_coq_position pos with
    | Some (Level n) -> n
    | _ -> assert false
    in
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

let unsafe_grammar_extend e reinit ext =
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

let make_rule r = [None, None, r]

(** An entry that checks we reached the end of the input. *)

let eoi_entry en =
  let e = Gram.entry_create ((Gram.Entry.name en) ^ "_eoi") in
  let symbs = [Symbols.snterm (Gram.Entry.obj en); Symbols.stoken Tok.EOI] in
  let act = Gram.action (fun _ x loc -> x) in
  maybe_uncurry (Gram.extend e) (None, make_rule [symbs, act]);
  e

let map_entry f en =
  let e = Gram.entry_create ((Gram.Entry.name en) ^ "_map") in
  let symbs = [Symbols.snterm (Gram.Entry.obj en)] in
  let act = Gram.action (fun x loc -> f x) in
  maybe_uncurry (Gram.extend e) (None, make_rule [symbs, act]);
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f x =
  let strm = Stream.of_string x in Gram.entry_parse f (Gram.parsable strm)

type gram_universe = string

let utables : (string, unit) Hashtbl.t =
  Hashtbl.create 97

let create_universe u =
  let () = Hashtbl.add utables u () in
  u

let uprim   = create_universe "prim"
let uconstr = create_universe "constr"
let utactic = create_universe "tactic"
let uvernac = create_universe "vernac"

let get_univ u =
  if Hashtbl.mem utables u then u
  else raise Not_found

(** A table associating grammar to entries *)
let gtable : Obj.t Gram.entry String.Map.t ref = ref String.Map.empty

let get_grammar (e : 'a Entry.t) : 'a Gram.entry =
  Obj.magic (String.Map.find (Entry.repr e) !gtable)

let set_grammar (e : 'a Entry.t) (g : 'a Gram.entry) =
  assert (not (String.Map.mem (Entry.repr e) !gtable));
  gtable := String.Map.add (Entry.repr e) (Obj.magic g) !gtable

let new_entry u s =
  let ename = u ^ ":" ^ s in
  let entry = Entry.create ename in
  let e = Gram.entry_create ename in
  let () = set_grammar entry e in
  e

let make_gen_entry u s = new_entry u s

module GrammarObj =
struct
  type ('r, _, _) obj = 'r Gram.entry
  let name = "grammar"
  let default _ = None
end

module Grammar = Register(GrammarObj)

let register_grammar = Grammar.register0
let genarg_grammar = Grammar.obj

let create_generic_entry (type a) u s (etyp : a raw_abstract_argument_type) : a Gram.entry =
  let e = new_entry u s in
  let Rawwit t = etyp in
  let () = Grammar.register0 t e in
  e

(* Initial grammar entries *)

module Prim =
  struct
    let gec_gen n = make_gen_entry uprim n

    (* Entries that can be referred via the string -> Gram.entry table *)
    (* Typically for tactic or vernac extensions *)
    let preident = gec_gen "preident"
    let ident = gec_gen "ident"
    let natural = gec_gen "natural"
    let index = gec_gen "index"
    let integer = gec_gen "integer"
    let bigint = Gram.entry_create "Prim.bigint"
    let string = gec_gen "string"
    let reference = make_gen_entry uprim "reference"
    let by_notation = Gram.entry_create "by_notation"
    let smart_global = Gram.entry_create "smart_global"

    (* parsed like ident but interpreted as a term *)
    let var = gec_gen "var"

    let name = Gram.entry_create "Prim.name"
    let identref = Gram.entry_create "Prim.identref"
    let pidentref = Gram.entry_create "Prim.pidentref"
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
    let gec_constr = make_gen_entry uconstr

    (* Entries that can be referred via the string -> Gram.entry table *)
    let constr = gec_constr "constr"
    let operconstr = gec_constr "operconstr"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let binder_constr = gec_constr "binder_constr"
    let ident = make_gen_entry uconstr "ident"
    let global = make_gen_entry uconstr "global"
    let sort = make_gen_entry uconstr "sort"
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

    (* Entries that can be referred via the string -> Gram.entry table *)
    (* Typically for tactic user extensions *)
    let open_constr =
      make_gen_entry utactic "open_constr"
    let constr_with_bindings =
      make_gen_entry utactic "constr_with_bindings"
    let bindings =
      make_gen_entry utactic "bindings"
    let hypident = Gram.entry_create "hypident"
    let constr_may_eval = make_gen_entry utactic "constr_may_eval"
    let constr_eval = make_gen_entry utactic "constr_eval"
    let uconstr =
      make_gen_entry utactic "uconstr"
    let quantified_hypothesis =
      make_gen_entry utactic "quantified_hypothesis"
    let int_or_var = make_gen_entry utactic "int_or_var"
    let red_expr = make_gen_entry utactic "red_expr"
    let simple_intropattern =
      make_gen_entry utactic "simple_intropattern"
    let clause_dft_concl = 
      make_gen_entry utactic "clause"


    (* Main entries for ltac *)
    let tactic_arg = Gram.entry_create "tactic:tactic_arg"
    let tactic_expr = make_gen_entry utactic "tactic_expr"
    let binder_tactic = make_gen_entry utactic "binder_tactic"

    let tactic = make_gen_entry utactic "tactic"

    (* Main entry for quotations *)
    let tactic_eoi = eoi_entry tactic

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
    let noedit_mode = gec_vernac "noedit_command"

    let () =
      let act_vernac = Gram.action (fun v loc -> Some (!@loc, v)) in
      let act_eoi = Gram.action (fun _ loc -> None) in
      let rule = [
        ([ Symbols.stoken Tok.EOI ], act_eoi);
        ([ Symbols.snterm (Gram.Entry.obj vernac) ], act_vernac );
      ] in
      maybe_uncurry (Gram.extend main_entry) (None, make_rule rule)

    let command_entry_ref = ref noedit_mode
    let command_entry =
      Gram.Entry.of_parser "command_entry"
        (fun strm -> Gram.parse_tokens_after_filter !command_entry_ref strm)

  end

let main_entry = Vernac_.main_entry

let set_command_entry e = Vernac_.command_entry_ref := e
let get_command_entry () = !Vernac_.command_entry_ref

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
   11,Extend.LeftA,false;
   10,Extend.RightA,false;
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

let compute_entry adjust forpat = function
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
  | ETOther (u,n) -> assert false

(* This computes the name of the level where to add a new rule *)
let interp_constr_entry_key forpat level =
  if level = 200 && not forpat then weaken_entry Constr.binder_constr, None
  else if forpat then weaken_entry Constr.pattern, Some level
  else weaken_entry Constr.operconstr, Some level

(* This computes the name to give to a production knowing the name and
   associativity of the level where it must be added *)
let interp_constr_prod_entry_key ass from forpat en =
  compute_entry (adjust_level ass from) forpat en

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
      Symbols.snterml (Gram.Entry.obj Constr.pattern,"200")
    else
      Symbols.snterml (Gram.Entry.obj Constr.operconstr,"200")
  else if is_self from typ then
      Symbols.sself
  else
    match typ with
    | ETConstrList (typ',[]) ->
        Symbols.slist1 (symbol_of_constr_prod_entry_key assoc from forpat (ETConstr typ'))
    | ETConstrList (typ',tkl) ->
        Symbols.slist1sep
          (symbol_of_constr_prod_entry_key assoc from forpat (ETConstr typ'),
          make_sep_rules tkl)
    | ETBinderList (false,[]) ->
        Symbols.slist1
	  (symbol_of_constr_prod_entry_key assoc from forpat (ETBinder false))
    | ETBinderList (false,tkl) ->
        Symbols.slist1sep
          (symbol_of_constr_prod_entry_key assoc from forpat (ETBinder false),
          make_sep_rules tkl)

    | _ ->
    match interp_constr_prod_entry_key assoc from forpat typ with
      | (eobj,None,_) -> Symbols.snterm (Gram.Entry.obj eobj)
      | (eobj,Some None,_) -> Symbols.snext
      | (eobj,Some (Some (lev,cur)),_) ->
          Symbols.snterml (Gram.Entry.obj eobj,constr_level lev)

(** Binding general entry keys to symbol *)

let tuplify l =
  List.fold_left (fun accu x -> Obj.repr (x, accu)) (Obj.repr ()) l

let rec adj : type a b c. (a, b, Loc.t -> Loc.t * c) adj -> _ = function
| Adj0 -> Obj.magic (fun accu f loc -> f (Obj.repr (to_coqloc loc, tuplify accu)))
| AdjS e -> Obj.magic (fun accu f x -> adj e (x :: accu) f)

let rec symbol_of_prod_entry_key : type s a. (s, a) symbol -> _ = function
  | Atoken t -> Symbols.stoken t
  | Alist1 s -> Symbols.slist1 (symbol_of_prod_entry_key s)
  | Alist1sep (s,sep) ->
      Symbols.slist1sep (symbol_of_prod_entry_key s, gram_token_of_string sep)
  | Alist0 s -> Symbols.slist0 (symbol_of_prod_entry_key s)
  | Alist0sep (s,sep) ->
      Symbols.slist0sep (symbol_of_prod_entry_key s, gram_token_of_string sep)
  | Aopt s -> Symbols.sopt (symbol_of_prod_entry_key s)
  | Aself -> Symbols.sself
  | Anext -> Symbols.snext
  | Aentry e ->
    let e = get_grammar e in
    Symbols.snterm (Gram.Entry.obj (weaken_entry e))
  | Aentryl (e, n) ->
    let e = get_grammar e in
    Symbols.snterml (Gram.Entry.obj (weaken_entry e), string_of_int n)
  | Arules rs -> Gram.srules' (symbol_of_rules rs [] (fun x -> I0 x))

and symbol_of_rule : type s a r. (s, a, r) Extend.rule -> _ = function
| Stop -> fun accu -> accu
| Next (r, s) -> fun accu -> symbol_of_rule r (symbol_of_prod_entry_key s :: accu)

and symbol_of_rules : type a. a Extend.rules -> _ = function
| Rule0 -> fun accu _ -> accu
| RuleS (r, e, rs) -> fun accu f ->
  let symb = symbol_of_rule r [] in
  let act = adj e [] f in
  symbol_of_rules rs ((symb, act) :: accu) (fun x -> IS (f x))

let level_of_snterml e = int_of_string (Symbols.snterml_level e)

let rec of_coq_action : type a r. (r, a, Loc.t -> r) Extend.rule -> a -> Gram.action = function
| Stop -> fun f -> Gram.action (fun loc -> f (to_coqloc loc))
| Next (r, _) -> fun f -> Gram.action (fun x -> of_coq_action r (f x))

let of_coq_production_rule : type a. a Extend.production_rule -> _ = function
| Rule (toks, act) -> (symbol_of_rule toks [], of_coq_action toks act)

let of_coq_single_extend_statement (lvl, assoc, rule) =
  (lvl, Option.map of_coq_assoc assoc, List.map of_coq_production_rule rule)

let of_coq_extend_statement (pos, st) =
  (Option.map of_coq_position pos, List.map of_coq_single_extend_statement st)

let grammar_extend e reinit ext =
  let ext = of_coq_extend_statement ext in
  unsafe_grammar_extend e reinit ext

let name_of_entry e = Entry.unsafe_of_name (Gram.Entry.name e)

let list_entry_names () = []

let epsilon_value f e =
  let r = Rule (Next (Stop, e), fun x _ -> f x) in
  let ext = of_coq_extend_statement (None, [None, None, [r]]) in
  let entry = G.entry_create "epsilon" in
  let () = maybe_uncurry (Gram.extend entry) ext in
  try Some (parse_string entry "") with _ -> None

(** Registering grammar of generic arguments *)

let () =
  let open Stdarg in
  let open Constrarg in
(*   Grammar.register0 wit_unit; *)
(*   Grammar.register0 wit_bool; *)
  Grammar.register0 wit_int (Prim.integer);
  Grammar.register0 wit_string (Prim.string);
  Grammar.register0 wit_pre_ident (Prim.preident);
  Grammar.register0 wit_int_or_var (Tactic.int_or_var);
  Grammar.register0 wit_intro_pattern (Tactic.simple_intropattern);
  Grammar.register0 wit_ident (Prim.ident);
  Grammar.register0 wit_var (Prim.var);
  Grammar.register0 wit_ref (Prim.reference);
  Grammar.register0 wit_quant_hyp (Tactic.quantified_hypothesis);
  Grammar.register0 wit_constr (Constr.constr);
  Grammar.register0 wit_uconstr (Tactic.uconstr);
  Grammar.register0 wit_open_constr (Tactic.open_constr);
  Grammar.register0 wit_constr_with_bindings (Tactic.constr_with_bindings);
  Grammar.register0 wit_bindings (Tactic.bindings);
(*   Grammar.register0 wit_hyp_location_flag; *)
  Grammar.register0 wit_red_expr (Tactic.red_expr);
  Grammar.register0 wit_tactic (Tactic.tactic);
  Grammar.register0 wit_ltac (Tactic.tactic);
  Grammar.register0 wit_clause_dft_concl (Tactic.clause_dft_concl);
  ()
