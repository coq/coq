(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open CErrors
open Names
open Libnames
open Constrexpr
open Extend
open Notation_gram
open Pcoq

(**********************************************************************)
(* This determines (depending on the associativity of the current
   level and on the expected associativity) if a reference to constr_n is
   a reference to the current level (to be translated into "SELF" on the
   left border and into "constr LEVEL n" elsewhere), to the level below
   (to be translated into "NEXT") or to an below wrt associativity (to be
   translated in camlp5 into "constr" without level) or to another level
   (to be translated into "constr LEVEL n")

   The boolean is true if the entry was existing _and_ empty; this to
   circumvent a weakness of camlp5 whose undo mechanism is not the
   converse of the extension mechanism *)

let constr_level = string_of_int

let default_levels =
  [200,Extend.RightA,false;
   100,Extend.RightA,false;
   99,Extend.RightA,true;
   90,Extend.RightA,true;
   10,Extend.LeftA,false;
   9,Extend.RightA,false;
   8,Extend.RightA,true;
   1,Extend.LeftA,false;
   0,Extend.RightA,false]

let default_pattern_levels =
  [200,Extend.RightA,true;
   100,Extend.RightA,false;
   99,Extend.RightA,true;
   90,Extend.RightA,true;
   10,Extend.LeftA,false;
   1,Extend.LeftA,false;
   0,Extend.RightA,false]

let default_constr_levels = (default_levels, default_pattern_levels)

let find_levels levels = function
  | InConstrEntry -> levels, String.Map.find "constr" levels
  | InCustomEntry s ->
     try levels, String.Map.find s levels
     with Not_found ->
     String.Map.add s ([],[]) levels, ([],[])

let save_levels levels custom lev =
  let s = match custom with InConstrEntry -> "constr" | InCustomEntry s -> s in
  String.Map.add s lev levels

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
  let open Pp in
  let pr_assoc = function
    | Extend.LeftA -> str "left"
    | Extend.RightA -> str "right"
    | Extend.NonA -> str "non" in
  user_err 
    (str "Level " ++ int p ++ str " is already declared " ++
     pr_assoc current ++ str " associative while it is now expected to be " ++
     pr_assoc expected ++ str " associative.")

let create_pos = function
  | None -> Extend.First
  | Some lev -> Extend.After (constr_level lev)

let find_position_gen current ensure assoc lev =
  match lev with
  | None ->
      current, (None, None, None, None)
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
	let updated = add_level None current in
	let assoc = create_assoc assoc in
        begin match !init with
        | None ->
	  (* Create the entry *)
	   updated, (Some (create_pos !after), Some assoc, Some (constr_level n), None)
        | _ ->
	  (* The reinit flag has been updated *)
	   updated, (Some (Extend.Level (constr_level n)), None, None, !init)
        end
      with
	  (* Nothing has changed *)
          Exit ->
	    (* Just inherit the existing associativity and name (None) *)
	    current, (Some (Extend.Level (constr_level n)), None, None, None)

let rec list_mem_assoc_triple x = function
  | [] -> false
  | (a,b,c) :: l -> Int.equal a x || list_mem_assoc_triple x l

let register_empty_levels accu forpat levels =
  let rec filter accu = function
  | [] -> ([], accu)
  | (where,n) :: rem ->
    let rem, accu = filter accu rem in
    let accu, (clev, plev) = find_levels accu where in
    let levels = if forpat then plev else clev in
    if not (list_mem_assoc_triple n levels) then
      let nlev, ans = find_position_gen levels true None (Some n) in
      let nlev = if forpat then (clev, nlev) else (nlev, plev) in
      (where, ans) :: rem, save_levels accu where nlev
    else rem, accu
  in
  filter accu levels

let find_position accu custom forpat assoc level =
  let accu, (clev, plev) = find_levels accu custom in
  let levels = if forpat then plev else clev in
  let nlev, ans = find_position_gen levels false assoc level in
  let nlev = if forpat then (clev, nlev) else (nlev, plev) in
  (ans, save_levels accu custom nlev)

(**************************************************************************)
(*
 * --- Note on the mapping of grammar productions to camlp5 actions ---
 *
 * Translation of environments: a production
 *   [ nt1(x1) ... nti(xi) ] -> act(x1..xi)
 * is written (with camlp5 conventions):
 *   (fun vi -> .... (fun v1 -> act(v1 .. vi) )..)
 * where v1..vi are the values generated by non-terminals nt1..nti.
 * Since the actions are executed by substituting an environment,
 * the make_*_action family build the following closure:
 *
 *      ((fun env ->
 *          (fun vi ->
 *             (fun env -> ...
 *
 *                  (fun v1 ->
 *                     (fun env -> gram_action .. env act)
 *                     ((x1,v1)::env))
 *                  ...)
 *             ((xi,vi)::env)))
 *         [])
 *)

(**********************************************************************)
(** Declare Notations grammar rules                                   *)

(**********************************************************************)
(* Binding constr entry keys to entries                               *)

(* Camlp5 levels do not treat NonA: use RightA with a NEXT on the left *)
let camlp5_assoc = function
  | Some NonA | Some RightA -> RightA
  | None | Some LeftA -> LeftA

let assoc_eq al ar = match al, ar with
| NonA, NonA
| RightA, RightA
| LeftA, LeftA -> true
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
  | (NumLevel n,BorderProd (Right,Some (NonA|LeftA))) ->
      Some None
  (* If RightA on the right-hand side, set to the explicit (current) level *)
  | (NumLevel n,BorderProd (Right,Some RightA)) ->
      Some (Some (n,true))
(* Compute production name on the left side *)
  (* If NonA on the left-hand side, adopt the current assoc ?? *)
  | (NumLevel n,BorderProd (Left,Some NonA)) -> None
  (* If the expected assoc is the current one, set to SELF *)
  | (NumLevel n,BorderProd (Left,Some a)) when assoc_eq a (camlp5_assoc assoc) ->
      None
  (* Otherwise, force the level, n or n-1, according to expected assoc *)
  | (NumLevel n,BorderProd (Left,Some a)) ->
    begin match a with
    | LeftA -> Some (Some (n, true))
    | _ -> Some None
    end
  (* None means NEXT *)
  | (NextLevel,_) -> Some None
(* Compute production name elsewhere *)
  | (NumLevel n,InternalProd) ->
    if from = n + 1 then Some None else Some (Some (n, Int.equal n from))

type _ target =
| ForConstr : constr_expr target
| ForPattern : cases_pattern_expr target

type prod_info = production_level * production_position

type (_, _) entry =
| TTName : ('self, lname) entry
| TTReference : ('self, qualid) entry
| TTBigint : ('self, Constrexpr.raw_natural_number) entry
| TTConstr : notation_entry * prod_info * 'r target -> ('r, 'r) entry
| TTConstrList : prod_info * Tok.t list * 'r target -> ('r, 'r list) entry
| TTPattern : int -> ('self, cases_pattern_expr) entry
| TTOpenBinderList : ('self, local_binder_expr list) entry
| TTClosedBinderList : Tok.t list -> ('self, local_binder_expr list list) entry

type _ any_entry = TTAny : ('s, 'r) entry -> 's any_entry

let constr_custom_entry : (string, Constrexpr.constr_expr) entry_command =
  create_entry_command "constr" (fun s st -> [s], st)
let pattern_custom_entry : (string, Constrexpr.cases_pattern_expr) entry_command =
  create_entry_command "pattern" (fun s st -> [s], st)

let custom_entry_locality = Summary.ref ~name:"LOCAL-CUSTOM-ENTRY" String.Set.empty
(** If the entry is present then local *)

let create_custom_entry ~local s =
  if List.mem s ["constr";"pattern";"ident";"global";"binder";"bigint"] then
    user_err Pp.(quote (str s) ++ str " is a reserved entry name.");
  let sc = "constr:"^s in
  let sp = "pattern:"^s in
  let _ = extend_entry_command constr_custom_entry sc in
  let _ = extend_entry_command pattern_custom_entry sp in
  let () = if local then custom_entry_locality := String.Set.add s !custom_entry_locality in
  ()

let find_custom_entry s =
  let sc = "constr:"^s in
  let sp = "pattern:"^s in
  try (find_custom_entry constr_custom_entry sc, find_custom_entry pattern_custom_entry sp)
  with Not_found -> user_err Pp.(str "Undeclared custom entry: " ++ str s ++ str ".")

let locality_of_custom_entry s = String.Set.mem s !custom_entry_locality

(* This computes the name of the level where to add a new rule *)
let interp_constr_entry_key : type r. _ -> r target -> int -> r Entry.t * int option =
  fun custom forpat level ->
  match custom with
  | InCustomEntry s ->
     (let (entry_for_constr, entry_for_patttern) = find_custom_entry s in
     match forpat with
     | ForConstr -> entry_for_constr, Some level
     | ForPattern -> entry_for_patttern, Some level)
  | InConstrEntry ->
  match forpat with
  | ForConstr ->
    if level = 200 then Constr.binder_constr, None
    else Constr.operconstr, Some level
  | ForPattern -> Constr.pattern, Some level

let target_entry : type s. notation_entry -> s target -> s Entry.t = function
| InConstrEntry ->
   (function
   | ForConstr -> Constr.operconstr
   | ForPattern -> Constr.pattern)
| InCustomEntry s ->
   let (entry_for_constr, entry_for_patttern) = find_custom_entry s in
   function
   | ForConstr -> entry_for_constr
   | ForPattern -> entry_for_patttern

let is_self from e = match e with
| (NumLevel n, BorderProd (Right, _ (* Some(NonA|LeftA) *))) -> false
| (NumLevel n, BorderProd (Left, _)) -> Int.equal from n
| _ -> false

let is_binder_level from e = match e with
| (NumLevel 200, (BorderProd (Right, _) | InternalProd)) -> from = 200
| _ -> false

let make_sep_rules = function
  | [tk] -> Atoken tk
  | tkl ->
  let rec mkrule : Tok.t list -> string rules = function
  | [] -> Rules ({ norec_rule = Stop }, fun _ -> (* dropped anyway: *) "")
  | tkn :: rem ->
    let Rules ({ norec_rule = r }, f) = mkrule rem in
    let r = { norec_rule = Next (r, Atoken tkn) } in
    Rules (r, fun _ -> f)
  in
  let r = mkrule (List.rev tkl) in
  Arules [r]

let symbol_of_target : type s. _ -> _ -> _ -> _ -> s target -> (s, s) symbol = fun custom p assoc from forpat ->
  if custom = InConstrEntry && is_binder_level from p then Aentryl (target_entry InConstrEntry forpat, "200")
  else if is_self from p then Aself
  else
    let g = target_entry custom forpat in
    let lev = adjust_level assoc from p in
    begin match lev with
    | None -> Aentry g
    | Some None -> Anext
    | Some (Some (lev, cur)) -> Aentryl (g, string_of_int lev)
    end

let symbol_of_entry : type s r. _ -> _ -> (s, r) entry -> (s, r) symbol = fun assoc from typ -> match typ with
| TTConstr (s, p, forpat) -> symbol_of_target s p assoc from forpat
| TTConstrList (typ', [], forpat) ->
  Alist1 (symbol_of_target InConstrEntry typ' assoc from forpat)
| TTConstrList (typ', tkl, forpat) ->
  Alist1sep (symbol_of_target InConstrEntry typ' assoc from forpat, make_sep_rules tkl)
| TTPattern p -> Aentryl (Constr.pattern, string_of_int p)
| TTClosedBinderList [] -> Alist1 (Aentry Constr.binder)
| TTClosedBinderList tkl -> Alist1sep (Aentry Constr.binder, make_sep_rules tkl)
| TTName -> Aentry Prim.name
| TTOpenBinderList -> Aentry Constr.open_binders
| TTBigint -> Aentry Prim.bigint
| TTReference -> Aentry Constr.global

let interp_entry forpat e = match e with
| ETProdName -> TTAny TTName
| ETProdReference -> TTAny TTReference
| ETProdBigint -> TTAny TTBigint
| ETProdConstr (s,p) -> TTAny (TTConstr (s, p, forpat))
| ETProdPattern p -> TTAny (TTPattern p)
| ETProdConstrList (p, tkl) -> TTAny (TTConstrList (p, tkl, forpat))
| ETProdBinderList ETBinderOpen -> TTAny TTOpenBinderList
| ETProdBinderList (ETBinderClosed tkl) -> TTAny (TTClosedBinderList tkl)

let cases_pattern_expr_of_name { CAst.loc; v = na } = CAst.make ?loc @@ match na with
  | Anonymous -> CPatAtom None
  | Name id   -> CPatAtom (Some (qualid_of_ident ?loc id))

type 'r env = {
  constrs : 'r list;
  constrlists : 'r list list;
  binders : cases_pattern_expr list;
  binderlists : local_binder_expr list list;
}

let push_constr subst v = { subst with constrs = v :: subst.constrs }

let push_item : type s r. s target -> (s, r) entry -> s env -> r -> s env = fun forpat e subst v ->
match e with
| TTConstr _ -> push_constr subst v
| TTName ->
  begin match forpat with
  | ForConstr -> { subst with binders = cases_pattern_expr_of_name v :: subst.binders }
  | ForPattern -> push_constr subst (cases_pattern_expr_of_name v)
  end
| TTPattern _ ->
  begin match forpat with
  | ForConstr -> { subst with binders = v :: subst.binders }
  | ForPattern -> push_constr subst v
  end
| TTOpenBinderList -> { subst with binderlists = v :: subst.binderlists }
| TTClosedBinderList _ -> { subst with binderlists = List.flatten v :: subst.binderlists }
| TTBigint ->
  begin match forpat with
  | ForConstr ->  push_constr subst (CAst.make @@ CPrim (Numeral (v,true)))
  | ForPattern -> push_constr subst (CAst.make @@ CPatPrim (Numeral (v,true)))
  end
| TTReference ->
  begin match forpat with
  | ForConstr  -> push_constr subst (CAst.make @@ CRef (v, None))
  | ForPattern -> push_constr subst (CAst.make @@ CPatAtom (Some v))
  end
| TTConstrList _ -> { subst with constrlists = v :: subst.constrlists }

type (_, _) ty_symbol =
| TyTerm : Tok.t -> ('s, string) ty_symbol
| TyNonTerm : 's target * ('s, 'a) entry * ('s, 'a) symbol * bool -> ('s, 'a) ty_symbol

type ('self, _, 'r) ty_rule =
| TyStop : ('self, 'r, 'r) ty_rule
| TyNext : ('self, 'a, 'r) ty_rule * ('self, 'b) ty_symbol -> ('self, 'b -> 'a, 'r) ty_rule
| TyMark : int * bool * int * ('self, 'a, 'r) ty_rule -> ('self, 'a, 'r) ty_rule

type 'r gen_eval = Loc.t -> 'r env -> 'r

let rec ty_eval : type s a. (s, a, Loc.t -> s) ty_rule -> s gen_eval -> s env -> a = function
| TyStop ->
  fun f env loc -> f loc env
| TyNext (rem, TyTerm _) ->
  fun f env _ -> ty_eval rem f env
| TyNext (rem, TyNonTerm (_, _, _, false)) ->
  fun f env _ -> ty_eval rem f env
| TyNext (rem, TyNonTerm (forpat, e, _, true)) ->
  fun f env v ->
    ty_eval rem f (push_item forpat e env v)
| TyMark (n, b, p, rem) ->
  fun f env ->
    let heads, constrs = List.chop n env.constrs in
    let constrlists, constrs =
      if b then
         (* We rearrange constrs = c1..cn rem and constrlists = [d1..dr e1..ep] rem' into
            constrs = e1..ep rem and constrlists [c1..cn d1..dr] rem' *)
         let constrlist = List.hd env.constrlists in
         let constrlist, tail = List.chop (List.length constrlist - p) constrlist in
         (heads @ constrlist) :: List.tl env.constrlists, tail @ constrs
      else
         (* We rearrange constrs = c1..cn e1..ep rem into
            constrs = e1..ep rem and add a constr list [c1..cn] *)
        let constrlist, tail = List.chop (n - p) heads in
        constrlist :: env.constrlists, tail @ constrs
    in
    ty_eval rem f { env with constrs; constrlists; } 

let rec ty_erase : type s a r. (s, a, r) ty_rule -> (s, a, r) Extend.rule = function
| TyStop -> Stop
| TyMark (_, _, _, r) -> ty_erase r
| TyNext (rem, TyTerm tok) -> Next (ty_erase rem, Atoken tok)
| TyNext (rem, TyNonTerm (_, _, s, _)) -> Next (ty_erase rem, s)

type ('self, 'r) any_ty_rule =
| AnyTyRule : ('self, 'act, Loc.t -> 'r) ty_rule -> ('self, 'r) any_ty_rule

let make_ty_rule assoc from forpat prods =
  let rec make_ty_rule = function
  | [] -> AnyTyRule TyStop
  | GramConstrTerminal tok :: rem ->
    let AnyTyRule r = make_ty_rule rem in
    AnyTyRule (TyNext (r, TyTerm tok))
  | GramConstrNonTerminal (e, var) :: rem ->
    let AnyTyRule r = make_ty_rule rem in
    let TTAny e = interp_entry forpat e in
    let s = symbol_of_entry assoc from e in
    let bind = match var with None -> false | Some _ -> true in
    AnyTyRule (TyNext (r, TyNonTerm (forpat, e, s, bind)))
  | GramConstrListMark (n, b, p) :: rem ->
    let AnyTyRule r = make_ty_rule rem in
    AnyTyRule (TyMark (n, b, p, r))
  in
  make_ty_rule (List.rev prods)

let target_to_bool : type r. r target -> bool = function
| ForConstr -> false
| ForPattern -> true

let prepare_empty_levels forpat (where,(pos,p4assoc,name,reinit)) =
  let empty = (pos, [(name, p4assoc, [])]) in
  ExtendRule (target_entry where forpat, reinit, empty)

let rec pure_sublevels' custom assoc from forpat level = function
| [] -> []
| GramConstrNonTerminal (e,_) :: rem ->
   let rem = pure_sublevels' custom assoc from forpat level rem in
   let push where p rem =
     match symbol_of_target custom p assoc from forpat with
     | Aentryl (_,i) when level <> Some (int_of_string i) -> (where,int_of_string i) :: rem
     | _ -> rem in
   (match e with
   | ETProdPattern i -> push InConstrEntry (NumLevel i,InternalProd) rem
   | ETProdConstr (s,p) -> push s p rem
   | _ -> rem)
| (GramConstrTerminal _ | GramConstrListMark _) :: rem -> pure_sublevels' custom assoc from forpat level rem

let make_act : type r. r target -> _ -> r gen_eval = function
| ForConstr -> fun notation loc env ->
  let env = (env.constrs, env.constrlists, env.binders, env.binderlists) in
  CAst.make ~loc @@ CNotation (notation, env)
| ForPattern -> fun notation loc env ->
  let env = (env.constrs, env.constrlists) in
  CAst.make ~loc @@ CPatNotation (notation, env, [])

let extend_constr state forpat ng =
  let custom,n,_,_ = ng.notgram_level in
  let assoc = ng.notgram_assoc in
  let (entry, level) = interp_constr_entry_key custom forpat n in
  let fold (accu, state) pt =
    let AnyTyRule r = make_ty_rule assoc n forpat pt in
    let symbs = ty_erase r in
    let pure_sublevels = pure_sublevels' custom assoc n forpat level pt in
    let isforpat = target_to_bool forpat in
    let needed_levels, state = register_empty_levels state isforpat pure_sublevels in
    let (pos,p4assoc,name,reinit), state = find_position state custom isforpat assoc level in
    let empty_rules = List.map (prepare_empty_levels forpat) needed_levels in
    let empty = { constrs = []; constrlists = []; binders = []; binderlists = [] } in
    let act = ty_eval r (make_act forpat ng.notgram_notation) empty in
    let rule = (name, p4assoc, [Rule (symbs, act)]) in
    let r = ExtendRule (entry, reinit, (pos, [rule])) in
    (accu @ empty_rules @ [r], state)
  in
  List.fold_left fold ([], state) ng.notgram_prods

let constr_levels = GramState.field ()

let extend_constr_notation ng state =
  let levels = match GramState.get state constr_levels with
  | None -> String.Map.add "constr" default_constr_levels String.Map.empty
  | Some lev -> lev
  in
  (* Add the notation in constr *)
  let (r, levels) = extend_constr levels ForConstr ng in
  (* Add the notation in cases_pattern *)
  let (r', levels) = extend_constr levels ForPattern ng in
  let state = GramState.set state constr_levels levels in
  (r @ r', state)

let constr_grammar : one_notation_grammar grammar_command =
  create_grammar_command "Notation" extend_constr_notation

let extend_constr_grammar ntn = extend_grammar_command constr_grammar ntn
