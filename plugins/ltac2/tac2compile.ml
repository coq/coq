(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Tac2expr
open Pp

let debug_flag, debug = CDebug.create_full ~name:"tac2compile" ()

let rawstr s = quote (str (String.escaped s))

(** Translation is done in 2 phases:
   - translate to out internal nontac_expr
     (represents expressions which evaluate to a Tac2ffi.valexpr,
      which is the case for all global definition bodies)
     This tracks info about previously compiled globals in a state,
     as well as info about names given to values obtained at dynlink time
     (because they can't be properly printed for Tac2dyn.Arg.Glb,
      or not nicely printed for kername)

   - print the nontac_expr
     this needs no state
*)

(* About name management:
   names ending with "__" are reserved for the compiler

   "x%d__" is a temporary
   (eg for the application in "match foo bar with ..."
    which is compiled to "(compile foo bar) >>= fun x0__ -> compile match ...")
   temporaries are used immediately so the counter resets
   every time we spill expressions to temporaries

   "%s_kn%d__" is a kernel name
   the "%s" is its label to make the ocaml code a bit more readable
   the "%d" is a global counter

   The compiled value for a kernel name is bound to either
   - "%s_kn%d_f__" when it's a function (ocaml type valexpr -> ... -> valexpr tactic)
   - "%s_kn%d_v__" otherwise (for cases like "Ltac2 foo := 0")

   "ext%d__" is used for the GTacExt argument, the "%d" is a global
   counter separate from the kername counter.

   "env__" is used for the Tac2interp.environment we need to build for GTacExt interpretation.

   "current_module__" is the name of the current OCaml module

   Capitalized names (modules, constructors) are from coq-core (mostly ltac2 plugin)
   The compiler does not translated Ltac2 types
   so instead of eg "Some 1" we have "ValBlk (0, [|ValInt 1|])"

   All other names are user names. As such to access coq-core values we must qualify them,
   eg "Tac2ffi.mk_closure_val" etc
*)

let temporary cnt = cnt+1, Id.of_string ("x"^string_of_int cnt^"__")

type binding_info =
  | Valexpr
  | Function of { arity : int }

module MkSpillId () : sig
  type t
  val make : Id.t -> t

  val print : t -> Pp.t
end =  struct
  type t = Id.t
  let make id = id

  let print = Id.print
end

module SpilledKn = MkSpillId ()
module SpilledExt = MkSpillId ()

type state =
  { spill_kns : (string * SpilledKn.t) KNmap.t
  (* first projection is kn -> "%s_kn%d" (without the "__" suffix, used to produce the _f__ name) *)
  ; spill_kn_cnt : int

  ; spill_ext : (Tac2dyn.Arg.glb * SpilledExt.t) list
  (* ext -> "ext%d__" *)
  ; spill_ext_cnt : int

  ; local_kns : (string * binding_info) KNmap.t
  }

type env =
  { user_bindings : binding_info Id.Map.t
  (* only contains real user names, no temporaries *)
  }

let empty_state = {
  spill_kns = KNmap.empty;
  spill_kn_cnt =0;
  spill_ext = [];
  spill_ext_cnt = 0;
  local_kns = KNmap.empty;
}

let empty_env = {
  user_bindings = Id.Map.empty;
}

let push_user_name na info env =
  match na with
  | Anonymous -> env
  | Name na ->
    assert (not (String.is_suffix "__" (Id.to_string na)));
    { user_bindings = Id.Map.add na info env.user_bindings }

(* currently used with same info for all names in the list *)
let push_user_names nas info env = List.fold_left (fun env na -> push_user_name na info env) env nas

let push_local_kn kn v env = { env with local_kns = KNmap.add kn v env.local_kns }

let spill_kn state kn =
  match KNmap.find_opt kn state.spill_kns with
  | Some s -> state, s
  | None ->
    let s = Label.to_string (KerName.label kn) in
    let s = match s.[0] with
      | 'A'..'Z' ->
        String.init (String.length s)
          (fun i -> if i = 0 then Char.lowercase_ascii s.[0] else s.[i])
      | _ -> s
    in
    let s = s ^ "_kn" ^ string_of_int state.spill_kn_cnt in
    let s' = SpilledKn.make (Id.of_string (s^"__")) in
    let state =
      { state with
        spill_kn_cnt = state.spill_kn_cnt + 1;
        spill_kns = KNmap.add kn (s, s') state.spill_kns; }
    in
    state, (s, s')

(* XXX we could add the extension tag as a prefix, eg "constr_ext42__",
   but we would need to ensure it only has valid characters for an ocaml id

   It may also be nice if we could deduplicate identical values. *)
let spill_ext state e =
  let s = Id.of_string ("ext"^string_of_int state.spill_ext_cnt^"__") in
  let s = SpilledExt.make s in
  let state =
    { state with
      spill_ext_cnt = state.spill_ext_cnt + 1;
      spill_ext = (e, s) :: state.spill_ext; }
  in
  state, s

let pp_ml_name ml =
  hv 2
    (str "{ Tac2expr.mltac_plugin = " ++ rawstr ml.mltac_plugin ++ str ";" ++ spc() ++
     str "mltac_tactic = " ++ rawstr ml.mltac_tactic ++ str " }")

let rec pp_arity n =
  if n = 1 then str "arity_one"
  else str "(arity_suc " ++ pp_arity (n-1) ++ str")"

let pp_arity n =
  assert (n >= 1);
  str "Tac2ffi.(" ++ pp_arity n ++ str ")"

let rec pp_binders = function
  | [] -> mt()
  | x :: rest -> spc() ++ Name.print x ++ pp_binders rest

type when_val  =
  | WhenString of string
  | WhenOpn of SpilledKn.t

type when_clause = When of when_val * Id.t

type pattern =
  | PatVar of Name.t
  | PatInt of int
  | PatStr of Id.t
  | PatCtor of int * pattern list (* non empty *)
  | PatOpn of Id.t * pattern list (* maybe empty *)
  | PatOr of pattern list
  | PatAs of pattern * Id.t

type reference =
  | LocalKn of (string * binding_info)
  | GlobalKn of SpilledKn.t

(** PURELY evaluates to a valexpr *)
type nontac_expr =
  | Atm of atom
  | Var of Id.t * binding_info option (* None for autogenerated temporaries *)
  | Ref of reference
  | Fun of Name.t list * tac_expr
  | Ctor of int * nontac_expr list (* non-mutable constructor *)
  | Opn of SpilledKn.t * nontac_expr list
  | PrjV of nontac_expr * int (* non-mutable projection *)
  | Prim of ml_tactic_name

(** evaluates to a valexpr tactic *)
and tac_expr_head =
  | Return of nontac_expr
  | App of nontac_expr * nontac_expr list
  | LetNoRec of (Name.t * tac_expr) list * tac_expr
  | LetRec of (Id.t * (Name.t list * tac_expr)) list * tac_expr
  | Match of nontac_expr * ((pattern * when_clause list) list * tac_expr) list
  | CtorMut of int * nontac_expr list (* mutable constructor *)
  | PrjMut of nontac_expr * int (* mutable projection *)
  | Set of nontac_expr * int * nontac_expr
  | Ext of binding_info Id.Map.t * SpilledExt.t

(** spilled_exprs >>= fun ids -> head_expr *)
and tac_expr = {
  spilled_exprs: (Id.t * tac_expr) list;
  head_expr: tac_expr_head;
}

let trivial_when : when_clause list = []
let trivial_when_pat pat = [pat, trivial_when]

let and_one_pattern pats nextp =
  let pats =
    List.map (fun (p, whenp) ->
        List.map (fun (nextp, nextwhen) -> (nextp :: p, List.append nextwhen whenp)) nextp)
      pats
  in
  List.flatten pats

let pattern_conjunction pats =
  let result = List.fold_left and_one_pattern ([[], trivial_when]) pats in
  List.map (on_fst List.rev) result

let rec pattern_of_glb_pat (state, cnt as acc) = function
  | GPatVar x -> acc, trivial_when_pat (PatVar x)
  | GPatAtm (AtmInt i) -> acc, trivial_when_pat (PatInt i)
  | GPatRef ({ cindx = Closed i }, []) -> acc, trivial_when_pat (PatInt i)
  | GPatAs (pat, x) ->
    let acc, pat = pattern_of_glb_pat acc pat in
    acc, List.map (fun (pat, cls) -> PatAs (pat, x), cls) pat

  | GPatAtm (AtmStr s) ->
    let cnt, x = temporary cnt in
    (state, cnt), [PatStr x, [When (WhenString s, x)]]

  | GPatRef ({ cindx = Open kn }, pats) ->
    let state, (_, kn) = spill_kn state kn in
    let cnt, x = temporary cnt in
    let acc, pats = List.fold_left_map pattern_of_glb_pat (state, cnt) pats in
    let pats = pattern_conjunction pats in
    let pats = List.map (fun (pats, w) -> (PatOpn (x, pats), When (WhenOpn kn, x) :: w)) pats in
    acc, pats

  | GPatRef ({ cindx = Closed i }, ((_ :: _) as pats)) ->
    let acc, pats = List.fold_left_map pattern_of_glb_pat acc pats in
    let pats = pattern_conjunction pats in
    acc, List.map (fun (pats,w) -> PatCtor (i, pats), w) pats

  | GPatOr pats ->
    (* BEWARE!

    [[
    | ((ValBlk (0, [|(ValStr x0__); _|])) |
       (ValBlk (0, [|_; (ValStr x0__)|])))
      when String.equal (Bytes.unsafe_to_string x0__) "s" ->
    ]]

    will NOT backtrack, so the branch will NOT be taken on eg ("", "s").
    That means we need to compile [("s", _) | (_, "s")] into 2 separate branches.

    Therefore we can only merge into an or-pattern when there is no when clause.

    Sadly this means or pattern compilation is exponential when string
    or open constructor patterns are involved. *)
    let acc, pats = List.fold_left_map pattern_of_glb_pat acc pats in
    let pats = List.flatten pats in
    let nowhen, withwhen = List.partition (fun (_,w) -> List.is_empty w) pats in
    let nowhen = List.map fst nowhen in
    let pats = match nowhen with
      | [] -> withwhen
      | [pat] -> (pat, []) :: withwhen
      | pats -> (PatOr pats, []) :: withwhen
    in
    acc, pats

let pattern_of_glb_pat state pat =
  let (state, _), pats = pattern_of_glb_pat (state, 0) pat in
  state, pats

let rec push_user_names_of_glb_pat env pat =
  let self = push_user_names_of_glb_pat in
  match pat with
  | GPatVar x -> push_user_name x Valexpr env
  | GPatAtm _ -> env
  | GPatAs (p, x) -> self (push_user_name (Name x) Valexpr env) p
  | GPatRef (_, pats) -> List.fold_left self env pats
  | GPatOr [] -> assert false
  | GPatOr (p::_) ->
    (* all the patterns in an or pattern bind the same names *)
    self env p

(* XXX collapse identical branches? eg when looking at 1 constructor
   of Constr.Unsafe.kind we get over a dozen trivial branches
   also if the default branch code is nontrivial the duplication probably hurts *)
let branches_of_case esInt esBlk =
  let int_branch i e = trivial_when_pat (PatInt i), e in
  let esInt = Array.mapi int_branch esInt in
  let block_branch i (nas, e) =
    let pats = Array.map_to_list (fun x -> PatVar x) nas in
    trivial_when_pat (PatCtor (i, pats)), e
  in
  let esBlk = Array.mapi block_branch esBlk in
  Array.to_list (Array.append esInt esBlk)

let branches_of_with brs def =
  let defbr = let na, e = def in
    trivial_when_pat (PatVar na), e
  in
  let one_branch (kn, (self,nas,e)) =
    let _, x = temporary 0 in
    let pat = PatOpn (x, Array.map_to_list (fun x -> PatVar x) nas) in
    let pat = match self with
      | Anonymous -> pat
      | Name self -> PatAs (pat, self)
    in
    let pat = [pat, [When (WhenOpn kn, x)]] in
    pat, e
  in
  List.append (List.map one_branch brs) [defbr]

let is_mutable_proj typ p =
  match snd (Tac2env.interp_type typ) with
  | GTydRec fields -> pi2 (List.nth fields p)
  | _ -> assert false

let reference state x =
  match KNmap.find_opt x state.local_kns with
  | None ->
    let state, (_, x) = spill_kn state x in
    state, GlobalKn x
  | Some info -> state, LocalKn info

(* Passing the global state and the nonval state purely functionally together would be messy
   as we may write
   "let acc, foo = do_foo (state, nonvalstate) in
    let state, bar = do_bar state (BAD, should be (fst acc)) in
    acc (BAD, should be (state, snd acc)), bli"
   or similar incorrect code

   Instead the global state is passed as a mutable ref.
*)
type env_and_mut_state = {
  state: state ref;
  env: env;
}

let with_state {state} f x =
  let s, v = f !state x in
  state := s;
  v

let with_env {env;state} f =
  let env = f env in
  {env;state}

let push_env f n v env = with_env env (fun env -> f n v env)

let is_pure_ctor = function
  | Other kn -> Tac2intern.is_pure_constructor kn
  | Tuple _ -> true

let rec nontac_expr env ((cnt, nonvals) as acc) e = match e with
  | GTacAtm a -> acc, Atm a
  | GTacVar x -> acc, Var (x, Id.Map.find_opt x env.env.user_bindings)
  | GTacRef x ->
    let r = with_state env reference x in
    acc, Ref r
  | GTacFun (nas,e) ->
    let e = tac_expr (push_env push_user_names nas Valexpr env) e in
    acc, Fun (nas, e)

  | GTacCst (kn, i, l) when is_pure_ctor kn ->
    let acc, l = List.fold_left_map (nontac_expr env) acc l in
    acc, Ctor (i, l)

  | GTacOpn (kn, l) ->
    let acc, l = List.fold_left_map (nontac_expr env) acc l in
    let (_, kn) = with_state env spill_kn kn in
    acc, Opn (kn, l)

  | GTacPrj (typ, sube, i) when not (is_mutable_proj typ i) ->
    let acc, sube = nontac_expr env acc sube in
    acc, PrjV (sube, i)

  | GTacPrm ml -> acc, Prim ml

  | GTacApp _ | GTacLet _ | GTacCse _
  | GTacPrj _ | GTacSet _ | GTacWth _ | GTacFullMatch _
  | GTacExt _ | GTacCst _ ->
    let cnt, id = temporary cnt in
    let e = tac_expr env e in
    let nonvals = (id, e) :: nonvals in
    (cnt, nonvals), Var (id, None)

and tac_expr env e =
  let (_, nonvals), e =
    let acc = (0, []) in
    match e with
    | GTacAtm _ | GTacVar _ | GTacRef _ | GTacFun _
    | GTacOpn _ | GTacPrm _ as e ->
      let acc, e = nontac_expr env acc e in
      acc, Return e

    | GTacCst (kn, i, l) ->
      let acc, l = List.fold_left_map (nontac_expr env) acc l in
      if is_pure_ctor kn then acc, Return (Ctor (i, l))
      else begin
        assert (not (List.is_empty l));
        acc, CtorMut (i, l)
      end

    | GTacPrj (typ, e, i) ->
      let acc, e = nontac_expr env acc e in
      if is_mutable_proj typ i
      then acc, PrjMut (e, i)
      else acc, Return (PrjV (e, i))

    | GTacApp (h, args) ->
      let acc, h = nontac_expr env acc h in
      let acc, args = List.fold_left_map (nontac_expr env) acc args in
      acc, App (h, args)

    | GTacLet (true, lets, e) ->
      let lets = lets |> List.filter_map (fun (na, e) ->
          match e with
          | GTacFun (bnd, e) ->
            begin match na with
            |  Anonymous ->
              (* "let rec _ := ..." seems good for nothing, just a syntax curiosity
                 lambda abstraction can't have effects so just drop it *)
              None
            | Name na ->
              Some (na, (bnd, e))
            end
          | _ -> assert false)
      in
      let env =
        List.fold_left (fun env (na, (bnd, _)) ->
            push_env push_user_name (Name na) (Function {arity=List.length bnd}) env)
          env lets
      in
      let lets = List.map (fun (na, (bnd, e)) ->
          let e = tac_expr (push_env push_user_names bnd Valexpr env) e in
          (na, (bnd, e)))
          lets
      in
      let e = tac_expr env e in
      acc, LetRec (lets, e)

    (* XXX detect when a let can be nontac_expr *)
    | GTacLet (false, bnd, e) ->
      let envbnd = push_env push_user_names (List.map fst bnd) Valexpr env in
      let bnd = List.map (fun (na, e) ->
          let e = tac_expr env e in
          (na, e))
          bnd
      in
      let e = tac_expr envbnd e in
      acc, LetNoRec (bnd, e)

    | GTacCse (e, _, esInt, esBlk) ->
      let acc, e = nontac_expr env acc e in
      let esInt = Array.map (tac_expr env) esInt in
      let esBlk = Array.map (fun (nas, e) ->
          let e = tac_expr (push_env push_user_names (Array.to_list nas) Valexpr env) e in
          (nas, e))
          esBlk
      in
      let brs = branches_of_case esInt esBlk in
      acc, Match (e, brs)

    | GTacWth {opn_match=e; opn_branch=brs; opn_default=def} ->
      let acc, e = nontac_expr env acc e in
      let brs = KNmap.map (fun (na,nas,e) ->
          let env = push_env push_user_name na Valexpr
              (push_env push_user_names (Array.to_list nas) Valexpr env)
          in
          let e = tac_expr env e in
          (na, nas, e))
          brs
      in
      let brs = List.map (fun (kn, v) ->
          let _, kn = with_state env spill_kn kn in
          kn,v)
          (KNmap.bindings brs)
      in
      let def =
        let na, def = def in
        let def = tac_expr (push_env push_user_name na Valexpr env) def in
        (na, def)
      in
      let brs = branches_of_with brs def in
      acc, Match (e, brs)

    | GTacFullMatch (e, brs) ->
      let acc, e = nontac_expr env acc e in
      let brs = List.map (fun (pat, e) ->
          let env = with_env env (fun env -> push_user_names_of_glb_pat env pat) in
          let pat = with_state env pattern_of_glb_pat pat in
          let e = tac_expr env e in
          (pat, e))
          brs
      in
      acc, Match (e, brs)

    | GTacSet (_,e1,i,e2) ->
      let acc, e1 = nontac_expr env acc e1 in
      let acc, e2 = nontac_expr env acc e2 in
      acc, Set (e1,i,e2)

    | GTacExt (ids,tag,v) ->
      let e = with_state env spill_ext (Glb (tag,v)) in
      let ids = Id.Map.bind (fun id -> Id.Map.get id env.env.user_bindings) ids in
      acc, Ext (ids, e)
  in
  { spilled_exprs = nonvals;
    head_expr = e; }

let nontac_expr env state acc e =
  let state = ref state in
  let acc, e = nontac_expr {env;state} acc e in
  !state, acc, e

let force_nontac_expr env state e =
  let state, (_, nonvals), e =
    nontac_expr env state (0, []) e
  in
  assert (List.is_empty nonvals);
  state, e

let translate_one_constant state kn =
  (* XXX skip if already compiled? but being locally available is important
     If we cache some info we can refer to TheOtherTmpModule.foo_kn42_f__
  *)
  let data = Tac2env.interp_global kn in
  let state, (kns, knid) = spill_kn state kn in
  let state, e = force_nontac_expr empty_env state data.gdata_expr in
  let na, bnd = match e with
    | Fun (nas,e) ->
      let knf = kns ^ "_f__" in
      knf, Function {arity=(List.length nas)}
    | _ ->
      let knv = kns ^ "_v__" in
      knv, Valexpr
  in
  let state = push_local_kn kn (na,bnd) state in
  state, (kn, knid, na, bnd, e)

let rec pp_binds pid pe = function
  | [] -> mt()
  | (id, e) :: rest ->
    pe e ++ str " >>= fun " ++ pid id ++ str " ->" ++ spc() ++ pp_binds pid pe rest

let rec pp_pat = function
  | PatVar x -> Name.print x
  | PatInt i -> str "(ValInt " ++ int i ++ str ")"
  | PatStr x -> surround (str "ValStr" ++ spc() ++ Id.print x)
  | PatCtor (i, pats) ->
    let pats =
      if List.for_all (function PatVar Anonymous -> true | _ -> false) pats
      then str "_"
      else
        hov 2
          (str "[|" ++ prlist_with_sep (fun () -> str";" ++ spc()) pp_pat pats ++ str "|]")
    in
    surround
      (str "ValBlk" ++ spc() ++
       surround
         (int i ++ str "," ++ spc() ++ pats))
  | PatOpn (x, pats) ->
    surround
      (str "ValOpn" ++ spc() ++
       surround
         (Id.print x ++ str "," ++ spc() ++
          hov 2 (str "[|" ++ prlist_with_sep (fun () -> str ";" ++ spc()) pp_pat pats ++ str "|]")))
  | PatOr pats ->
    assert (not (List.is_empty pats));
    surround (prlist_with_sep (fun () -> spc() ++ str "|" ++ spc()) pp_pat pats)
  | PatAs (pat, x) -> surround (pp_pat pat ++ spc() ++ str "as" ++ spc() ++ Id.print x)

let pp_when (When (w, id)) =
  match w with
  | WhenString s ->
    hov 2
      (str "String.equal"  ++ spc() ++
       (surround (str "Bytes.unsafe_to_string" ++ spc() ++ Id.print id)) ++ spc() ++
       rawstr s)
  | WhenOpn kn ->
    hov 2 (str "KerName.equal" ++ spc() ++ Id.print id ++ spc() ++ SpilledKn.print kn)

let pp_when_clauses w =
  if List.is_empty w then mt()
  else
    spc() ++
    hov 2
      (str "when" ++ spc() ++
       prlist_with_sep (fun () -> spc() ++ str "&&" ++ spc()) pp_when w)

let pp_mk_closure_val arity f =
  surround
    (str "Tac2ffi.mk_closure_val" ++ spc() ++
     pp_arity arity ++ spc() ++ f)

let pp_var x = function
  | None | Some Valexpr -> Id.print x
  | Some (Function {arity}) -> pp_mk_closure_val arity (Id.print x)

let rebind_interpreter_env ids =
  let ppenv =
    Id.Map.fold (fun id info ppenv ->
        surround
          (str "Tac2interp.push_id" ++ spc() ++ ppenv ++ spc() ++
           str "(Id.of_string " ++ rawstr (Id.to_string id) ++ str ")" ++ spc() ++
           pp_var id (Some info)))
      ids
      (str "Tac2interp.empty_environment")
  in
  str "let env__ =" ++ spc() ++ ppenv ++ spc() ++ str "in"

(* XXX use with_frame where appropriate *)

let pp_valexpr_of_bound pp = function
  | Valexpr -> pp
  | Function {arity} -> pp_mk_closure_val arity pp

(* produce a ocaml term of type valexpr *)
let rec pp_nontac_expr = function
  | Atm (AtmInt i) | Ctor (i, []) -> str "(ValInt " ++ int i ++ str")"
  | Atm (AtmStr s) -> str "(ValBlk (Bytes.of_string " ++ rawstr s ++ str"))"
  | Var (x, info) -> pp_var x info
  | Ref (GlobalKn kn) -> surround (str "Tac2interp.eval_global" ++ spc() ++ SpilledKn.print kn)
  | Ref (LocalKn (name, info)) -> pp_valexpr_of_bound (str name) info
  | Fun (nas, e) ->
    pp_mk_closure_val (List.length nas)
      (surround
         (h (str "fun" ++ pp_binders nas ++ str " ->") ++ spc() ++
          pp_expr e))
  | Ctor (i, es) -> str "(ValBlk (" ++ int i ++ str ", [|" ++ pp_val_list es ++ str "|]))"
  | PrjV (e, i) ->
    surround
      (str "Tac2ffi.Valexpr.field" ++ spc() ++ pp_nontac_expr e ++ spc() ++ int i)
  | Opn (kn, es) ->
    surround
      (str "Tac2ffi.of_open" ++ spc() ++
       surround
         (SpilledKn.print kn ++ str "," ++ spc() ++
          hov 2 (str "[|" ++ pp_val_list es ++ str "|]")))
  | Prim ml ->
    surround (str "Tac2env.interp_primitive" ++ spc() ++ pp_ml_name ml)

(* produce a ocaml term of type valexpr tactic *)
and pp_expr e =
  let { spilled_exprs = nonvals; head_expr = e; } = e in
  if List.is_empty nonvals then pp_head_expr e
  else surround (pp_binds Id.print pp_expr nonvals ++ pp_head_expr e)

and pp_head_expr = function
  | Return e -> surround (str "PV.tclUNIT" ++ spc() ++ pp_nontac_expr e)

  | App (h, args) ->
    let hinfo = match h with
      | Ref (LocalKn info) -> Some info
      | Ref (GlobalKn _) -> None
      | Var (id, info) ->
        (* NB: if temporary, it's always bound to a valexpr not a function *)
        Option.map (fun info -> Id.to_string id, info) info
      | _ -> None
    in
    let hinfo = match hinfo with
      | None -> None
      | Some (x, Valexpr) -> None
      | Some (x, Function {arity}) ->
        (* XXX do something intelligent in the < and > cases? *)
        if List.length args = arity then Some x
        else None
    in
    begin match hinfo with
    | None ->
      surround
        (str "Tac2ffi.apply_val" ++ spc() ++ pp_nontac_expr h ++ spc() ++
         surround (str "[" ++ pp_val_list args ++ str "]"))
    | Some x ->
      surround
        (str x ++ spc() ++ prlist_with_sep spc pp_nontac_expr args)
    end

  (* special print for 1 letin as we don't need to avoid name capture *)
  | LetNoRec ([na,e1], e2) ->
    surround (pp_binds Name.print pp_expr [na,e1] ++ pp_expr e2)

  | LetNoRec (bnd, e) ->
    let _, bnd =
      List.fold_left_map (fun cnt (na,e) ->
          match na with
          | Name x -> cnt, (x, na, e)
          | Anonymous ->
            (* evaluated for effects, eg "let r1 := !r1 with _ := incr r1 in ..."
               should act like C "r1++" *)
            let cnt, x = temporary cnt in
            cnt, (x, Anonymous, e))
        0 bnd
    in
    let na1, e1, rest = match bnd with
      | [] -> assert false
      | (na1, _, e1) :: rest -> na1, e1, rest
    in
    let pr_one_let na e = Id.print na ++ str " =" ++ spc() ++ pp_expr e in
    hv 2
      (str "(" ++
       hov 2 (str "let " ++ pr_one_let na1 e1) ++ spc() ++
       prlist (fun (na,_,e) -> hov 2 (str "and " ++ pr_one_let na e) ++ spc())  rest ++
       str "in" ++ spc() ++
       prlist (fun (x, na, _) ->
           Id.print x ++ str " >>= fun " ++ Name.print na ++ str " ->" ++ spc())
         bnd ++
       pp_expr e ++
       str ")")


  | LetRec (lets, e) ->
    (* pr_one_let does not including the leading "let rec " / "and " *)
    let pr_one_let (na, (bnd, e)) =
      hov 1 (Id.print na ++ pp_binders bnd ++ str " =") ++ spc () ++
      pp_expr e ++ spc()
    in
    surround
      (hv 0
         (str "let rec " ++ prlist_with_sep (fun () -> str "and ") pr_one_let lets ++
          str "in" ++ spc()) ++
       pp_expr e)

  | Match (e, brs) ->
    let brs = List.flatten (List.map (fun (pats, e) -> List.map (fun p -> p, e) pats) brs) in
    if List.is_empty brs
    then str "assert false"
    else
      (* the match is usually not exhaustive on valexpr
         but that just means we get Match_failure exception instead of doing an explicit assert false
         if something goes wrong (Match_failure is critical just like Assert_failure btw) *)
      let pp_branch ((pat, whenpat), e) =
        hov 2
          (str "|" ++ spc() ++
           h (pp_pat pat) ++ pp_when_clauses whenpat ++ spc() ++ str "->" ++ spc() ++
           pp_expr e) ++
        spc()
      in
      hov 2
        (str "begin match" ++ spc() ++ pp_nontac_expr e ++ str " with" ++ spc() ++
         hv 0 (prlist pp_branch brs ++ str "end"))

  | CtorMut (i, es) ->
    (* Not sure if we actually need to thunk this one but let's be safe. *)
    hv 1
      (str "(PV.tclUNIT () >>= fun () ->" ++ spc() ++
       str "PV.tclUNIT" ++ spc() ++
       surround
         (str "ValBlk" ++ spc() ++
          surround
            (int i ++ str "," ++ spc() ++
             hov 2
               (str "[|" ++ pp_val_list es ++ str "|]"))) ++
       str ")")

  | PrjMut (e, i) ->
    (* Don't forget to delay the side effect with a thunk! *)
    hv 1
      (str "(PV.tclUNIT () >>= fun () ->" ++ spc() ++
       str "PV.tclUNIT" ++ spc() ++
       surround
         (str "Tac2ffi.Valexpr.field" ++ spc() ++ pp_nontac_expr e ++ spc() ++ int i) ++
       str ")")

  | Set (e1,i,e2) ->
    (* Don't forget to delay the side effect with a thunk! *)
    hv 1
      (str "(PV.tclUNIT () >>= fun () ->" ++ spc() ++
       h (str "let () = Tac2ffi.Valexpr.set_field" ++ spc() ++
          pp_nontac_expr e1 ++ spc() ++ int i ++ spc() ++
          pp_nontac_expr e2 ++ spc()) ++
       str "in" ++ spc() ++
       str "PV.tclUNIT (ValInt 0))")

  | Ext (ids, v) ->
    surround
      (hv 0 (rebind_interpreter_env ids) ++ spc() ++
       str "Tac2interp.eval_glb_ext env__" ++ spc() ++ SpilledExt.print v)

and pp_val_list l = prlist_with_sep (fun () -> str";" ++ spc()) pp_nontac_expr l

let pp_compile_info na =
  hov 2
    (str "{" ++ spc() ++
     str "Tac2env.source =" ++ spc() ++
     hov 2 (str "current_module__" ++ str " ^ \".\"" ++ spc () ++ str "^ " ++ rawstr na) ++ spc() ++
     str "}")

let pp_one_constant (kn, knid, na, bnd, e) =
  let pp = match e with
    | Fun (nas, e) ->
      hv 2
        (str "let " ++ h (str na ++ pp_binders nas) ++ str " =" ++ spc() ++
         pp_expr e) ++ fnl() ++ fnl()
    | _ -> hv 2 (str "let " ++ str na ++ str " =" ++ spc() ++ pp_nontac_expr e) ++ fnl() ++ fnl()
  in
  let pp_set_compiled =
    hv 2 (str "let () = Tac2env.set_compiled_global" ++ spc() ++
          SpilledKn.print knid ++ spc() ++
          pp_compile_info na ++ spc() ++
          pp_valexpr_of_bound (str na) bnd) ++ fnl()
  in
  let pp =
    str "(** " ++ KerName.print kn ++ str " *)" ++ fnl() ++ fnl() ++
    pp ++
    pp_set_compiled
  in
  pp

let prelude prefix =
  str "let current_module__ = " ++ rawstr prefix ++ fnl() ++ fnl() ++
  str "open Names" ++ fnl() ++
  str "open Ltac2_plugin" ++ fnl() ++
  str "open Tac2ffi" ++ fnl() ++
  str "module PV = Proofview" ++ fnl() ++
  str "open PV.Notations" ++ fnl()

let pp_spilled_kns env =
  let kns = Array.of_list (KNmap.bindings env.spill_kns) in
  let pp =
    prvecti (fun i (kn,(_,s)) ->
        str "(* " ++ KerName.print kn ++ str " *)" ++ fnl() ++
        str "let " ++ SpilledKn.print s ++ str " = " ++
        str "(!Tac2compile.spilled_kns).(" ++ int i ++ str ")" ++ fnl() ++ fnl())
      kns
  in
  let kns = Array.map fst kns in
  kns, pp

let pp_spilled_exts env =
  let exts = Array.of_list env.spill_ext in
  let pp =
    prvecti (fun i (_ext, s) ->
        str "let " ++ SpilledExt.print s ++ str " = " ++
        str "(!Tac2compile.spilled_exts).(" ++ int i ++ str ")" ++ fnl())
      exts
  in
  let exts = Array.map fst exts in
  exts, pp

let pp_code prefix knl =
  let state = empty_state in
  let state, csts = List.fold_left_map translate_one_constant state knl in
  let kns, ppkns = pp_spilled_kns state in
  let exts, ppexts = pp_spilled_exts state in
  let pp = prlist_with_sep fnl pp_one_constant csts in
  let pp =
    prelude prefix ++ fnl() ++
    ppkns ++ fnl() ++
    ppexts ++ fnl() ++
    pp
  in
  kns, exts, pp

let get_expr_deps e =
  let rec aux deps = function
  | GTacAtm _ | GTacVar _ -> deps
  | GTacRef kn -> KNset.add kn deps
  | GTacFun (_,e) -> aux deps e
  | GTacApp (e,es) -> List.fold_left aux (aux deps e) es
  | GTacLet (_,l,e) -> List.fold_left (fun deps (_,e) -> aux deps e) (aux deps e) l
  | GTacCst (_,_,es) -> List.fold_left aux deps es
  | GTacCse (e,_,es1,es2) ->
    let deps = aux deps e in
    let deps = Array.fold_left aux deps es1 in
    Array.fold_left (fun deps (_,e) -> aux deps e) deps es2
  | GTacPrj (_,e,_) -> aux deps e
  | GTacSet (_,e1,_,e2) -> let deps = aux deps e1 in aux deps e2
  | GTacOpn (_,es) -> List.fold_left aux deps es
  | GTacWth {opn_match=e; opn_branch=brs; opn_default=(_,def)} ->
    let deps = aux deps e in
    let deps = KNmap.fold (fun _ (_,_,e) deps -> aux deps e) brs deps in
    aux deps def
  | GTacFullMatch (e, l) ->
    let deps = aux deps e in
    List.fold_left (fun deps (_,e) -> aux deps e) deps l
  | GTacExt _ -> deps
  (* Too hard to get the deps in TacExt, they just won't get
     automatically compiled in recursive mode *)
  | GTacPrm _ -> deps
  in
  aux KNset.empty e

(* Produce a list of kernames in reverse dependency order: the first
   depends on nothing, the second may depend on the first, etc.

   This function adds [kn] and all its dependencies to the list. *)
let rec get_dependencies ((visited, skipped_mut, knl) as acc) kn =
  if KNset.mem kn visited then acc
  else
    let data = Tac2env.interp_global kn in
    let skipped_mut =
      if data.gdata_mutable
      then KNset.add kn skipped_mut
      else skipped_mut
    in
    let kndeps = get_expr_deps data.gdata_expr in
    KNset.fold (fun kn acc -> get_dependencies acc kn)
      kndeps
      (KNset.add kn visited, skipped_mut, kn :: knl)

let warn_skipped_mut = CWarnings.create ~name:"tac2compile-skipped-mutable" ~category:CWarnings.CoreCategories.ltac2
    (fun skipped_mut ->
       str "Skipped compilation of mutable definitions" ++ spc() ++
       prlist_with_sep spc Tac2print.pr_tacref (KNset.elements skipped_mut))

let get_recursive_kns knl =
  let _, skipped_mut, knl = List.fold_left get_dependencies (KNset.empty, KNset.empty, []) knl in
  let () = if not (KNset.is_empty skipped_mut) then warn_skipped_mut skipped_mut in
  knl

let my_temp_dir = ref None

let force_temp_dir () = match !my_temp_dir with
  | Some d -> d
  | None ->
    let d = CUnix.mktemp_dir "tac2compile_" "" in
    my_temp_dir := Some d;
    d

let () = at_exit (fun () ->
    if not (CDebug.get_flag debug_flag) && Option.has_some !my_temp_dir then
      try
        let d = Option.get !my_temp_dir in
        Array.iter (fun f -> Sys.remove (Filename.concat d f)) (Sys.readdir d);
        Unix.rmdir d
      with e ->
        Feedback.msg_warning
          Pp.(str "tac2compile: failed to cleanup: " ++
              str(Printexc.to_string e) ++ fnl()))

let get_ml_filename () =
  let temp_dir = force_temp_dir () in
  let filename, ch = Filename.open_temp_file ~temp_dir "f" ".ml" in
  let prefix = Filename.chop_extension (Filename.basename filename) in
  let prefix = String.init (String.length prefix) (fun i -> if i = 0 then 'F' else prefix.[i]) in
  filename, ch, prefix

let error_compiler_failed e =
  let msg = match e with
  | Inl (Unix.WEXITED 127) -> Pp.(strbrk "The OCaml compiler was not found. Make sure it is installed, together with findlib.")
  | Inl (Unix.WEXITED n) ->
     Pp.(strbrk "Ltac2 compiler exited with status" ++ str" " ++ int n
         ++ strbrk (if n = 2 then " (in case of stack overflow, increasing stack size (typically with \"ulimit -s\") often helps)" else ""))
  | Inl (Unix.WSIGNALED n) -> Pp.(strbrk "Ltac2 compiler killed by signal" ++ str" " ++ int n)
  | Inl (Unix.WSTOPPED n) -> Pp.(strbrk "Ltac2 compiler stopped by signal" ++ str" " ++ int n)
  | Inr e -> Pp.(strbrk "Ltac2 compiler failed with error: " ++ strbrk (Unix.error_message e))
  in
  CErrors.user_err msg

let include_dirs () =
  (* TODO make this work in -boot / dev shim mode *)
  let open Boot.Env in
  let env = init () in
  (* engine for Proofview, kernel for Names *)
  List.map (fun x -> Path.to_string (native_cmi env x))
    [ "kernel"; "engine"; "plugins/ltac2" ]

let call_compiler fml =
  let f = Filename.chop_extension fml in
  let fo = Dynlink.adapt_filename (f ^ ".cmo") in
  let remove f = if Sys.file_exists f then Sys.remove f in
  remove (f ^ ".cmi");
  remove fo;
  let initial_args =
    if Dynlink.is_native then
      ["opt"; "-shared"]
    else
      ["ocamlc"; "-c"]
  in
  let include_dirs = List.flatten (List.map (fun x -> ["-I"; x]) (include_dirs())) in
  let args =
    initial_args @
    ["-g"] @
    ["-o"; fo;
     "-w"; "-a"] @
    include_dirs @
    ["-impl"; fml]
  in
  let ocamlfind = Envars.ocamlfind() in
  debug Pp.(fun () -> str (ocamlfind ^ " " ^ String.concat " " args));
  try
    let res = CUnix.sys_command ocamlfind args in
    match res with
    | WEXITED 0 -> fo
    | WEXITED _ | WSIGNALED _ | WSTOPPED _ ->
      error_compiler_failed (Inl res)
  with Unix.Unix_error (e,_,_) -> error_compiler_failed (Inr e)

let spilled_kns = ref [||]

let spilled_exts = ref [||]

let link_compiled kns exts fo =
  spilled_kns := kns;
  spilled_exts := exts;
  let () = if Dynlink.is_native then Dynlink.loadfile fo else Mltop.load_module fo in
  spilled_kns := [||];
  spilled_exts := [||]

(* XXX JIT mode? *)
let compile ~recursive knl =
  let () = List.iter (fun kn ->
      (* Error if explicitly asked to compile a mutable, warn if recursively *)
      if (Tac2env.interp_global kn).gdata_mutable then
        CErrors.user_err
          Pp.(str "Not allowed to compile mutable " ++ Tac2print.pr_tacref kn ++ str "."))
      knl
  in
  let knl =
    if recursive then get_recursive_kns knl
    else knl
  in
  let file, ch, prefix = get_ml_filename () in
  let kns, exts, pp = pp_code prefix knl in
  let fch = Format.formatter_of_out_channel ch in
  Pp.pp_with fch pp;
  close_out ch;
  let r = call_compiler file in
  link_compiled kns exts r
