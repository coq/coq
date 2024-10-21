(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Notationextern
open Notation_gram
open Procq

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
  [200,Gramlib.Gramext.RightA,true;
   100,Gramlib.Gramext.RightA,false;
   99,Gramlib.Gramext.RightA,true;
   90,Gramlib.Gramext.RightA,true;
   10,Gramlib.Gramext.LeftA,false;
   9,Gramlib.Gramext.RightA,false;
   8,Gramlib.Gramext.RightA,true;
   1,Gramlib.Gramext.LeftA,false;
   0,Gramlib.Gramext.RightA,false]

let default_pattern_levels =
  [200,Gramlib.Gramext.RightA,true;
   100,Gramlib.Gramext.RightA,false;
   99,Gramlib.Gramext.RightA,true;
   90,Gramlib.Gramext.RightA,true;
   10,Gramlib.Gramext.LeftA,false;
   1,Gramlib.Gramext.LeftA,false;
   0,Gramlib.Gramext.RightA,false]

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
  | Gramlib.Gramext.LeftA, Some (Gramlib.Gramext.RightA | Gramlib.Gramext.NonA) -> false
  | Gramlib.Gramext.RightA, Some Gramlib.Gramext.LeftA -> false
  | _ -> true

let create_assoc = function
  | None -> Gramlib.Gramext.RightA
  | Some a -> a

exception NotationLevelMismatch
  of entry_level * Gramlib.Gramext.g_assoc * Gramlib.Gramext.g_assoc

let () = CErrors.register_handler (function
  | NotationLevelMismatch (p, current, expected) ->
      Some Pp.(str "Level " ++ int p ++ str " is already declared to have " ++
        Gramlib.Gramext.pr_assoc current ++
        str " while it is now expected to have " ++
        Gramlib.Gramext.pr_assoc expected ++ str ".")
  | _ -> None)

let error_level_assoc p current expected =
  raise @@ NotationLevelMismatch (p, current, expected)

type position = NewFirst | NewAfter of int | ReuseFirst | ReuseLevel of int

let create_pos = function
  | None -> NewFirst
  | Some lev -> NewAfter lev

let find_position_gen current ensure assoc lev =
  match lev with
  | None ->
    current, (ReuseFirst, None, None, None)
  | Some n ->
    let after = ref None in
    let init = ref None in
    let rec add_level q = function
      | (p,_,_ as pa)::l when p > n -> pa :: add_level (Some p) l
      | (p,a,reinit)::l when Int.equal p n ->
        if reinit then
          let a' = create_assoc assoc in
          (init := Some (a', q); (p,a',false)::l)
        else if admissible_assoc (a,assoc) then
          raise_notrace Exit
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
          updated, (create_pos !after, Some assoc, Some (constr_level n), None)
        | _ ->
          (* The reinit flag has been updated *)
          updated, (ReuseLevel n, None, None, !init)
      end
    with
    (* Nothing has changed *)
      Exit ->
      (* Just inherit the existing associativity and name (None) *)
      current, (ReuseLevel n, None, None, None)

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
  let (l,accu) = filter accu levels in
  List.rev l, accu

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
let camlp5_assoc =
  let open Gramlib.Gramext in function
    | Some NonA | Some RightA -> RightA
    | None | Some LeftA -> LeftA

let assoc_eq al ar =
  let open Gramlib.Gramext in
  match al, ar with
  | NonA, NonA
  | RightA, RightA
  | LeftA, LeftA -> true
  | _, _ -> false

(** [adjust_level assoc fromlev prod] where [assoc] and [fromlev] are the name
   and associativity of the level where to add the rule; the meaning of
   the result is

     DefaultLevel = entry name
     NextLevel = NEXT
     NumLevel n = constr LEVEL n *)
let adjust_level custom assoc {notation_entry = custom'; notation_level = fromlev} p =
  let open Gramlib.Gramext in match p with
(* If a level in a different grammar, no other choice than denoting it by absolute level *)
  | (NumLevel n,_) when not (notation_entry_eq custom custom') -> NumLevel n
(* If a default level in a different grammar, the entry name is ok *)
  | (DefaultLevel,InternalProd) ->
    if notation_entry_eq custom InConstrEntry then NumLevel 200 else DefaultLevel
  | (DefaultLevel,BorderProd _) when not (notation_entry_eq custom custom') ->
    if notation_entry_eq custom InConstrEntry then NumLevel 200 else DefaultLevel
(* Associativity is None means force the level *)
  | (NumLevel n,BorderProd (_,None)) -> NumLevel n
  | (DefaultLevel,BorderProd (_,None)) -> assert false
(* Compute production name on the right side *)
  (* If NonA or LeftA on the right-hand side, set to NEXT *)
  | ((NumLevel _ | DefaultLevel),BorderProd (Right,Some (NonA|LeftA))) -> NextLevel
  (* If RightA on the right-hand side, set to the explicit (current) level *)
  | (NumLevel n,BorderProd (Right,Some RightA)) -> NumLevel n
  | (DefaultLevel,BorderProd (Right,Some RightA)) -> NumLevel fromlev
(* Compute production name on the left side *)
  (* If NonA on the left-hand side, adopt the current assoc ?? *)
  | ((NumLevel _ | DefaultLevel),BorderProd (Left,Some NonA)) -> DefaultLevel
  (* If the expected assoc is the current one, set to SELF *)
  | ((NumLevel _ | DefaultLevel),BorderProd (Left,Some a)) when assoc_eq a (camlp5_assoc assoc) ->
      DefaultLevel
  (* Otherwise, force the level, n or n-1, according to expected assoc *)
  | (NumLevel n,BorderProd (Left,Some LeftA)) -> NumLevel n
  | ((NumLevel _ | DefaultLevel),BorderProd (Left,Some _)) -> NextLevel
  (* None means NEXT *)
  | (NextLevel,_) -> assert (notation_entry_eq custom custom'); NextLevel
(* Compute production name elsewhere *)
  | (NumLevel n,InternalProd) ->
    if fromlev = n + 1 then NextLevel else NumLevel n

type _ target =
| ForConstr : constr_expr target
| ForPattern : cases_pattern_expr target

type prod_info = production_level * production_position

type (_, _) entry =
| TTIdent : ('self, lident) entry
| TTName : ('self, lname) entry
| TTGlobal : ('r, qualid) entry
| TTBigint : ('r, string) entry
| TTBinder : bool -> ('self, kinded_cases_pattern_expr) entry
| TTConstr : notation_entry * prod_info * 'r target -> ('r, 'r) entry
| TTConstrList : notation_entry * prod_info * (bool * string) list * 'r target -> ('r, 'r list) entry
| TTPattern : int -> ('self, cases_pattern_expr) entry
| TTOpenBinderList : ('self, local_binder_expr list) entry
| TTClosedBinderListPure : (bool * string) list -> ('self, local_binder_expr list list) entry
| TTClosedBinderListOther : ('self, 'a) entry * (bool * string) list -> ('self, 'a list) entry

type _ any_entry = TTAny : ('s, 'r) entry -> 's any_entry

let constr_custom_entry : (string, Constrexpr.constr_expr) entry_command =
  create_entry_command "constr" { eext_fun = (fun s st -> [s], st); eext_eq = (==) (* FIXME *) }
let pattern_custom_entry : (string, Constrexpr.cases_pattern_expr) entry_command =
  create_entry_command "pattern" { eext_fun = (fun s st -> [s], st); eext_eq = (==) (* FIXME *) }

let custom_entry_locality = Summary.ref ~name:"LOCAL-CUSTOM-ENTRY" String.Set.empty
(** If the entry is present then local *)

let create_custom_entry ~local s =
  if List.mem s ["constr";"pattern";"ident";"global";"binder";"bigint"] then
    user_err Pp.(quote (str s) ++ str " is a reserved entry name.");
  let sc = "custom:"^s in
  let sp = "custom_pattern:"^s in
  let _ = extend_entry_command constr_custom_entry sc in
  let _ = extend_entry_command pattern_custom_entry sp in
  let () = if local then custom_entry_locality := String.Set.add s !custom_entry_locality in
  ()

let find_custom_entry s =
  let sc = "custom:"^s in
  let sp = "custom_pattern:"^s in
  try (find_custom_entry constr_custom_entry sc, find_custom_entry pattern_custom_entry sp)
  with Not_found -> user_err Pp.(str "Undeclared custom entry: " ++ str s ++ str ".")

let exists_custom_entry s = match find_custom_entry s with
| _ -> true
| exception e when CErrors.noncritical e -> false

let locality_of_custom_entry s = String.Set.mem s !custom_entry_locality

(** This computes the name of the level where to add a new rule *)
let interp_constr_entry_key : type r. _ -> r target -> r Entry.t * int option =
  fun {notation_entry = custom; notation_level = level} forpat ->
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
    else Constr.term, Some level
  | ForPattern -> Constr.pattern, Some level

let target_entry : type s. notation_entry -> s target -> s Entry.t = function
| InConstrEntry ->
   (function
   | ForConstr -> Constr.term
   | ForPattern -> Constr.pattern)
| InCustomEntry s ->
   let (entry_for_constr, entry_for_patttern) = find_custom_entry s in
   function
   | ForConstr -> entry_for_constr
   | ForPattern -> entry_for_patttern

let is_self custom {notation_entry = custom'; notation_level = fromlev} e =
  notation_entry_eq custom custom' && match e with
  | (NumLevel n, BorderProd (Right, _ (* Some(NonA|LeftA) *))) -> false
  | (NumLevel n, BorderProd (Left, _)) -> Int.equal fromlev n
  | _ -> false

let is_binder_level custom {notation_entry = custom'; notation_level = fromlev} e =
  match e with
  | (NumLevel 200, (BorderProd (Right, _) | InternalProd)) ->
    custom = InConstrEntry && custom' = InConstrEntry && fromlev = 200
  | _ -> false

let make_pattern (keyword,s) =
   if keyword then TPattern (Tok.PKEYWORD s) else
     match NumTok.Unsigned.parse_string s with
     | Some n -> TPattern (Tok.PNUMBER (Some n))
     | None ->
     match String.unquote_coq_string s with
     | Some s -> TPattern (Tok.PSTRING (Some s))
     | None -> TPattern (Tok.PIDENT (Some s))

let make_sep_rules tkl =
  Procq.Symbol.tokens (List.map make_pattern tkl)

type ('s, 'a) mayrec_symbol =
| MayRecNo : ('s, Gramlib.Grammar.norec, 'a) Symbol.t -> ('s, 'a) mayrec_symbol
| MayRecMay : ('s, Gramlib.Grammar.mayrec, 'a) Symbol.t -> ('s, 'a) mayrec_symbol

let symbol_of_target : type s. _ -> _ -> _ -> _ -> s target -> (s, s) mayrec_symbol = fun custom p assoc from forpat ->
  if is_binder_level custom from p
  then
    (* Prevent self *)
    MayRecNo (Procq.Symbol.nterml (target_entry custom forpat) "200")
  else if is_self custom from p then MayRecMay Procq.Symbol.self
  else
    let g = target_entry custom forpat in
    let lev = adjust_level custom assoc from p in
    begin match lev with
    | DefaultLevel -> MayRecNo (Procq.Symbol.nterm g)
    | NextLevel -> MayRecMay Procq.Symbol.next
    | NumLevel lev -> MayRecNo (Procq.Symbol.nterml g (string_of_int lev))
    end

let rec symbol_of_entry : type s r. _ -> _ -> (s, r) entry -> (s, r) mayrec_symbol = fun assoc from typ -> match typ with
| TTConstr (s, p, forpat) -> symbol_of_target s p assoc from forpat
| TTConstrList (s, typ', [], forpat) ->
  begin match symbol_of_target s typ' assoc from forpat with
  | MayRecNo s -> MayRecNo (Procq.Symbol.list1 s)
  | MayRecMay s -> MayRecMay (Procq.Symbol.list1 s) end
| TTConstrList (s, typ', tkl, forpat) ->
  begin match symbol_of_target s typ' assoc from forpat with
  | MayRecNo s -> MayRecNo (Procq.Symbol.list1sep s (make_sep_rules tkl) false)
  | MayRecMay s -> MayRecMay (Procq.Symbol.list1sep s (make_sep_rules tkl) false) end
| TTPattern p -> MayRecNo (Procq.Symbol.nterml Constr.pattern (string_of_int p))
| TTOpenBinderList -> MayRecNo (Procq.Symbol.nterm Constr.open_binders)
| TTClosedBinderListPure [] -> MayRecNo (Procq.Symbol.list1 (Procq.Symbol.nterm Constr.binder))
| TTClosedBinderListPure tkl -> MayRecNo (Procq.Symbol.list1sep (Procq.Symbol.nterm Constr.binder) (make_sep_rules tkl) false)
| TTClosedBinderListOther (typ,[]) ->
  begin match symbol_of_entry assoc from typ with
  | MayRecNo s -> MayRecNo (Procq.Symbol.list1 s)
  | MayRecMay s -> MayRecMay (Procq.Symbol.list1 s) end
| TTClosedBinderListOther (typ,tkl) ->
  begin match symbol_of_entry assoc from typ with
  | MayRecNo s -> MayRecNo (Procq.Symbol.list1sep s (make_sep_rules tkl) false)
  | MayRecMay s -> MayRecMay (Procq.Symbol.list1sep s (make_sep_rules tkl) false) end
| TTIdent -> MayRecNo (Procq.Symbol.nterm Prim.identref)
| TTName -> MayRecNo (Procq.Symbol.nterm Prim.name)
| TTBinder true -> MayRecNo (Procq.Symbol.nterm Constr.one_open_binder)
| TTBinder false -> MayRecNo (Procq.Symbol.nterm Constr.one_closed_binder)
| TTBigint -> MayRecNo (Procq.Symbol.nterm Prim.bignat)
| TTGlobal -> MayRecNo (Procq.Symbol.nterm Constr.global)

let rec interp_entry forpat e = match e with
| ETProdIdent -> TTAny TTIdent
| ETProdName -> TTAny TTName
| ETProdGlobal -> TTAny TTGlobal
| ETProdBigint -> TTAny TTBigint
| ETProdOneBinder o -> TTAny (TTBinder o)
| ETProdConstr (s,p) -> TTAny (TTConstr (s, p, forpat))
| ETProdPattern p -> TTAny (TTPattern p)
| ETProdConstrList (s, p, tkl) -> TTAny (TTConstrList (s, p, tkl, forpat))
| ETProdBinderList ETBinderOpen -> TTAny TTOpenBinderList
| ETProdBinderList (ETBinderClosed (None, tkl)) -> TTAny (TTClosedBinderListPure tkl)
| ETProdBinderList (ETBinderClosed (Some e, tkl)) ->
  let TTAny e = interp_entry forpat e in TTAny (TTClosedBinderListOther (e, tkl))

let cases_pattern_expr_of_id { CAst.loc; v = id } =
  CAst.make ?loc @@ CPatAtom (Some (qualid_of_ident ?loc id))

let cases_pattern_expr_of_name { CAst.loc; v = na } = CAst.make ?loc @@ match na with
  | Anonymous -> CPatAtom None
  | Name id   -> CPatAtom (Some (qualid_of_ident ?loc id))

type 'r env = {
  constrs : 'r list;
  constrlists : 'r list list;
  binders : kinded_cases_pattern_expr list;
  binderlists : local_binder_expr list list;
}

let push_constr subst v = { subst with constrs = v :: subst.constrs }

let push_item : type s r. s target -> (s, r) entry -> s env -> r -> s env = fun forpat e subst v ->
match e with
| TTConstr _ -> push_constr subst v
| TTIdent -> { subst with binders = (cases_pattern_expr_of_id v, Glob_term.Explicit) :: subst.binders }
| TTName -> { subst with binders = (cases_pattern_expr_of_name v, Glob_term.Explicit) :: subst.binders }
| TTPattern _ -> { subst with binders = (v, Glob_term.Explicit) :: subst.binders }
| TTBinder o -> { subst with binders = v :: subst.binders }
| TTOpenBinderList -> { subst with binderlists = v :: subst.binderlists }
| TTClosedBinderListPure _ -> { subst with binderlists = List.flatten v :: subst.binderlists }
| TTClosedBinderListOther (TTIdent, _) -> { subst with binderlists = List.map (fun a -> CLocalPattern (cases_pattern_expr_of_id a)) v :: subst.binderlists }
| TTClosedBinderListOther (TTName, _) -> { subst with binderlists = List.map (fun a -> CLocalPattern (cases_pattern_expr_of_name a)) v :: subst.binderlists }
| TTClosedBinderListOther (TTPattern _, _) -> { subst with binderlists = List.map (fun a -> CLocalPattern a) v :: subst.binderlists }
| TTClosedBinderListOther _ -> user_err (Pp.str "Invalid binder list entry.")
| TTBigint ->
  begin match forpat with
  | ForConstr ->  push_constr subst (CAst.make @@ CPrim (Number (NumTok.Signed.of_int_string v)))
  | ForPattern -> push_constr subst (CAst.make @@ CPatPrim (Number (NumTok.Signed.of_int_string v)))
  end
| TTGlobal ->
  begin match forpat with
  | ForConstr  -> push_constr subst (CAst.make @@ CRef (v, None))
  | ForPattern -> push_constr subst (CAst.make @@ CPatAtom (Some v))
  end
| TTConstrList _ -> { subst with constrlists = v :: subst.constrlists }

type (_, _) ty_symbol =
| TyTerm : 'a Tok.p -> ('s, 'a) ty_symbol
| TyNonTerm : 's target * ('s, 'a) entry * ('s, 'a) mayrec_symbol * bool -> ('s, 'a) ty_symbol

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

type ('s, 'a, 'r) mayrec_rule =
| MayRecRNo : ('s, Gramlib.Grammar.norec, 'a, 'r) Rule.t -> ('s, 'a, 'r) mayrec_rule
| MayRecRMay : ('s, Gramlib.Grammar.mayrec, 'a, 'r) Rule.t -> ('s, 'a, 'r) mayrec_rule

let rec ty_erase : type s a r. (s, a, r) ty_rule -> (s, a, r) mayrec_rule = function
| TyStop -> MayRecRNo Rule.stop
| TyMark (_, _, _, r) -> ty_erase r
| TyNext (rem, TyTerm tok) ->
   begin match ty_erase rem with
   | MayRecRNo rem -> MayRecRMay (Rule.next rem (Symbol.token tok))
   | MayRecRMay rem -> MayRecRMay (Rule.next rem (Symbol.token tok)) end
| TyNext (rem, TyNonTerm (_, _, s, _)) ->
   begin match ty_erase rem, s with
   | MayRecRNo rem, MayRecNo s -> MayRecRMay (Rule.next rem s)
   | MayRecRNo rem, MayRecMay s -> MayRecRMay (Rule.next rem s)
   | MayRecRMay rem, MayRecNo s -> MayRecRMay (Rule.next rem s)
   | MayRecRMay rem, MayRecMay s -> MayRecRMay (Rule.next rem s) end

type ('self, 'r) any_ty_rule =
| AnyTyRule : ('self, 'act, Loc.t -> 'r) ty_rule -> ('self, 'r) any_ty_rule

let make_ty_rule assoc from forpat prods =
  let rec make_ty_rule = function
  | [] -> AnyTyRule TyStop
  | GramConstrTerminal (kw,s) :: rem ->
    let AnyTyRule r = make_ty_rule rem in
    let TPattern tk = make_pattern (kw,s) in
    AnyTyRule (TyNext (r, TyTerm tk))
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
  let empty = match pos with
  | ReuseFirst -> Procq.Reuse (None, [])
  | ReuseLevel n -> Procq.Reuse (Some (constr_level n), [])
  | NewFirst -> Procq.Fresh (Gramlib.Gramext.First, [(name, p4assoc, [])])
  | NewAfter n -> Procq.Fresh (Gramlib.Gramext.After (constr_level n), [(name, p4assoc, [])])
  in
  match reinit with
  | None ->
    ExtendRule (target_entry where forpat, empty)
  | Some (assoc, pos) ->
    let pos = match pos with None -> Gramlib.Gramext.First | Some n -> Gramlib.Gramext.After (constr_level n) in
    let reinit = (assoc, pos) in
    ExtendRuleReinit (target_entry where forpat, reinit, empty)

let different_levels (custom,opt_level) (custom',string_level) =
  match opt_level with
  | None -> true
  | Some level -> not (notation_entry_eq custom custom') || level <> int_of_string string_level

let rec pure_sublevels' assoc from forpat level = function
| [] -> []
| GramConstrNonTerminal (e,_) :: rem ->
   let rem = pure_sublevels' assoc from forpat level rem in
   let push where p rem =
     match symbol_of_target where p assoc from forpat with
     | MayRecNo sym ->
       (match Procq.level_of_nonterm sym with
        | None -> rem
        | Some i ->
          if different_levels (from.notation_entry,level) (where,i) then
            (where,int_of_string i) :: rem
          else rem)
     | _ -> rem in
   (match e with
   | ETProdPattern i -> push InConstrEntry (NumLevel i,InternalProd) rem
   | ETProdConstr (s,p) -> push s p rem
   | _ -> rem)
| (GramConstrTerminal _ | GramConstrListMark _) :: rem -> pure_sublevels' assoc from forpat level rem

let make_act : type r. r target -> _ -> r gen_eval = function
| ForConstr -> fun notation loc env ->
  let env = (env.constrs, env.constrlists, env.binders, env.binderlists) in
  CAst.make ~loc @@ CNotation (None, notation, env)
| ForPattern -> fun notation loc env ->
  let env = (env.constrs, env.constrlists, env.binders) in
  CAst.make ~loc @@ CPatNotation (None, notation, env, [])

let extend_constr state forpat ng =
  let {notation_entry = custom; notation_level = _} as fromlev,_ = ng.notgram_level in
  let assoc = ng.notgram_assoc in
  let (entry, level) = interp_constr_entry_key fromlev forpat in
  let fold (accu, state) pt =
    let AnyTyRule r = make_ty_rule assoc fromlev forpat pt in
    let pure_sublevels = pure_sublevels' assoc fromlev forpat level pt in
    let isforpat = target_to_bool forpat in
    let needed_levels, state = register_empty_levels state isforpat pure_sublevels in
    let (pos,p4assoc,name,reinit), state = find_position state custom isforpat assoc level in
    let empty_rules = List.map (prepare_empty_levels forpat) needed_levels in
    let empty = { constrs = []; constrlists = []; binders = []; binderlists = [] } in
    let act = ty_eval r (make_act forpat ng.notgram_notation) empty in
    let rule =
      let r = match ty_erase r with
        | MayRecRNo symbs -> Procq.Production.make symbs act
        | MayRecRMay symbs -> Procq.Production.make symbs act
      in
      let rule = name, p4assoc, [r] in
      match pos with
      | NewFirst -> Procq.Fresh (Gramlib.Gramext.First, [rule])
      | NewAfter n -> Procq.Fresh (Gramlib.Gramext.After (constr_level n), [rule])
      | ReuseFirst -> Procq.Reuse (None, [r])
      | ReuseLevel n -> Procq.Reuse (Some (constr_level n), [r])
    in
    let r = match reinit with
      | None ->
        ExtendRule (entry, rule)
      | Some (assoc, pos) ->
        let pos = match pos with None -> Gramlib.Gramext.First | Some n -> Gramlib.Gramext.After (constr_level n) in
        let reinit = (assoc, pos) in
        ExtendRuleReinit (entry, reinit, rule)
    in
    (accu @ empty_rules @ [r], state)
  in
  List.fold_left fold ([], state) ng.notgram_prods

let constr_levels = GramState.field "constr_levels"

let is_disjunctive_pattern_rule ng =
  String.is_sub "( _ | " (snd ng.notgram_notation) 0

let warn_disj_pattern_notation =
  let open Pp in
  let pp ng = str "Use of " ++ Notation.pr_notation ng.notgram_notation ++
              str " Notation is deprecated as it is inconsistent with pattern syntax." in
  CWarnings.create ~name:"disj-pattern-notation" ~category:CWarnings.CoreCategories.syntax ~default:CWarnings.Disabled pp

let extend_constr_notation ng state =
  let levels = match GramState.get state constr_levels with
  | None -> String.Map.add "constr" default_constr_levels String.Map.empty
  | Some lev -> lev
  in
  (* Add the notation in constr *)
  let (r, levels) = extend_constr levels ForConstr ng in
  (* Add the notation in cases_pattern, unless it would disrupt *)
  (* parsing nested disjunctive patterns. *)
  let (r', levels) =
    if is_disjunctive_pattern_rule ng then begin
       warn_disj_pattern_notation ng;
       ([], levels)
    end else extend_constr levels ForPattern ng in
  let state = GramState.set state constr_levels levels in
  (r @ r', state)

let constr_grammar : one_notation_grammar grammar_command =
  create_grammar_command "Notation" { gext_fun = extend_constr_notation; gext_eq = (==) (* FIXME *) }

let extend_constr_grammar ntn = extend_grammar_command constr_grammar ntn
