open Printf
open Globnames
open Libobject
open Entries
open Decl_kinds
open Declare

(**
   - Get types of existentials ;
   - Flatten dependency tree (prefix order) ;
   - Replace existentials by De Bruijn indices in term, applied to the right arguments ;
   - Apply term prefixed by quantification on "existentials".
*)

open Term
open Context
open Vars
open Names
open Evd
open Pp
open Errors
open Util

let declare_fix_ref = ref (fun _ _ _ _ _ _ -> assert false)
let declare_definition_ref = ref (fun _ _ _ _ _ -> assert false)

let trace s =
  if !Flags.debug then msg_debug s
  else ()

let succfix (depth, fixrels) =
  (succ depth, List.map succ fixrels)

let check_evars env evm =
  Evar.Map.iter
  (fun key evi ->
   let (loc,k) = evar_source key evm in
     match k with
     | Evar_kinds.QuestionMark _
     | Evar_kinds.ImplicitArg (_,_,false) -> ()
     | _ ->
       Pretype_errors.error_unsolvable_implicit loc env evm key None)
  (Evd.undefined_map evm)

type oblinfo =
  { ev_name: int * Id.t;
    ev_hyps: named_context;
    ev_status: Evar_kinds.obligation_definition_status;
    ev_chop: int option;
    ev_src: Evar_kinds.t Loc.located;
    ev_typ: types;
    ev_tac: unit Proofview.tactic option;
    ev_deps: Int.Set.t }

(* spiwack: Store field for internalizing ev_tac in evar_infos' evar_extra. *)
let evar_tactic = Store.field ()

(** Substitute evar references in t using De Bruijn indices,
  where n binders were passed through. *)

let subst_evar_constr evs n idf t = 
  let seen = ref Int.Set.empty in
  let transparent = ref Id.Set.empty in
  let evar_info id = List.assoc_f Evar.equal id evs in
  let rec substrec (depth, fixrels) c = match kind_of_term c with
    | Evar (k, args) ->
	let { ev_name = (id, idstr) ;
	      ev_hyps = hyps ; ev_chop = chop } =
	  try evar_info k
	  with Not_found ->
	    anomaly ~label:"eterm" (Pp.str "existential variable " ++ int (Evar.repr k) ++ str " not found")
	in
        seen := Int.Set.add id !seen;
	  (* Evar arguments are created in inverse order,
	     and we must not apply to defined ones (i.e. LetIn's)
	  *)
	let args =
	  let n = match chop with None -> 0 | Some c -> c in
	  let (l, r) = List.chop n (List.rev (Array.to_list args)) in
	    List.rev r
	in
	let args =
	  let rec aux hyps args acc =
	     match hyps, args with
		 ((_, None, _) :: tlh), (c :: tla) ->
		   aux tlh tla ((substrec (depth, fixrels) c) :: acc)
	       | ((_, Some _, _) :: tlh), (_ :: tla) ->
		   aux tlh tla acc
	       | [], [] -> acc
	       | _, _ -> acc (*failwith "subst_evars: invalid argument"*)
	  in aux hyps args []
	in
	  if List.exists
            (fun x -> match kind_of_term x with
            | Rel n -> Int.List.mem n fixrels
            | _ -> false) args
          then
	    transparent := Id.Set.add idstr !transparent;
	  mkApp (idf idstr, Array.of_list args)
    | Fix _ ->
	map_constr_with_binders succfix substrec (depth, 1 :: fixrels) c
    | _ -> map_constr_with_binders succfix substrec (depth, fixrels) c
  in
  let t' = substrec (0, []) t in
    t', !seen, !transparent


(** Substitute variable references in t using De Bruijn indices,
  where n binders were passed through. *)
let subst_vars acc n t =
  let var_index id = Util.List.index Id.equal id acc in
  let rec substrec depth c = match kind_of_term c with
    | Var v -> (try mkRel (depth + (var_index v)) with Not_found -> c)
    | _ -> map_constr_with_binders succ substrec depth c
  in
    substrec 0 t

(** Rewrite type of an evar ([ H1 : t1, ... Hn : tn |- concl ])
    to a product : forall H1 : t1, ..., forall Hn : tn, concl.
    Changes evars and hypothesis references to variable references.
*)
let etype_of_evar evs hyps concl =
  let rec aux acc n = function
      (id, copt, t) :: tl ->
	let t', s, trans = subst_evar_constr evs n mkVar t in
	let t'' = subst_vars acc 0 t' in
	let rest, s', trans' = aux (id :: acc) (succ n) tl in
	let s' = Int.Set.union s s' in
	let trans' = Id.Set.union trans trans' in
	  (match copt with
	      Some c -> 
		let c', s'', trans'' = subst_evar_constr evs n mkVar c in
		let c' = subst_vars acc 0 c' in
		  mkNamedProd_or_LetIn (id, Some c', t'') rest,
		Int.Set.union s'' s',
		Id.Set.union trans'' trans'
	    | None ->
		mkNamedProd_or_LetIn (id, None, t'') rest, s', trans')
    | [] ->
	let t', s, trans = subst_evar_constr evs n mkVar concl in
	  subst_vars acc 0 t', s, trans
  in aux [] 0 (List.rev hyps)

let trunc_named_context n ctx =
  let len = List.length ctx in
    List.firstn (len - n) ctx

let rec chop_product n t =
  if Int.equal n 0 then Some t
  else
    match kind_of_term t with
      | Prod (_, _, b) ->  if noccurn 1 b then chop_product (pred n) (Termops.pop b) else None
      | _ -> None

let evar_dependencies evm oev =
  let one_step deps =
    Evar.Set.fold (fun ev s ->
      let evi = Evd.find evm ev in
      let deps' = evars_of_filtered_evar_info evi in
      if Evar.Set.mem oev deps' then
	invalid_arg ("Ill-formed evar map: cycle detected for evar " ^ string_of_existential oev)
      else Evar.Set.union deps' s)
      deps deps
  in
  let rec aux deps =
    let deps' = one_step deps in
      if Evar.Set.equal deps deps' then deps
      else aux deps'
  in aux (Evar.Set.singleton oev)
      
let move_after (id, ev, deps as obl) l = 
  let rec aux restdeps = function
    | (id', _, _) as obl' :: tl -> 
	let restdeps' = Evar.Set.remove id' restdeps in
	  if Evar.Set.is_empty restdeps' then
	    obl' :: obl :: tl
	  else obl' :: aux restdeps' tl
    | [] -> [obl]
  in aux (Evar.Set.remove id deps) l
    
let sort_dependencies evl =
  let rec aux l found list =
    match l with
    | (id, ev, deps) as obl :: tl ->
	let found' = Evar.Set.union found (Evar.Set.singleton id) in
	  if Evar.Set.subset deps found' then
	    aux tl found' (obl :: list)
	  else aux (move_after obl tl) found list
    | [] -> List.rev list
  in aux evl Evar.Set.empty []

open Environ

let eterm_obligations env name evm fs ?status t ty = 
  (* 'Serialize' the evars *)
  let nc = Environ.named_context env in
  let nc_len = Context.named_context_length nc in
  let evm = Evarutil.nf_evar_map_undefined evm in
  let evl = Evarutil.non_instantiated evm in
  let evl = Evar.Map.bindings evl in
  let evl = List.map (fun (id, ev) -> (id, ev, evar_dependencies evm id)) evl in
  let sevl = sort_dependencies evl in
  let evl = List.map (fun (id, ev, _) -> id, ev) sevl in
  let evn =
    let i = ref (-1) in
      List.rev_map (fun (id, ev) -> incr i;
		      (id, (!i, Id.of_string
			      (Id.to_string name ^ "_obligation_" ^ string_of_int (succ !i))),
		       ev)) evl
  in
  let evts =
    (* Remove existential variables in types and build the corresponding products *)
    List.fold_right
      (fun (id, (n, nstr), ev) l ->
	 let hyps = Evd.evar_filtered_context ev in
	 let hyps = trunc_named_context nc_len hyps in
	 let evtyp, deps, transp = etype_of_evar l hyps ev.evar_concl in
	 let evtyp, hyps, chop =
	   match chop_product fs evtyp with
	   | Some t -> t, trunc_named_context fs hyps, fs
	   | None -> evtyp, hyps, 0
	 in
	 let loc, k = evar_source id evm in
	 let status = match k with Evar_kinds.QuestionMark o -> Some o | _ -> status in
	 let status, chop = match status with
	   | Some (Evar_kinds.Define true as stat) ->
	       if not (Int.equal chop fs) then Evar_kinds.Define false, None
	       else stat, Some chop
	   | Some s -> s, None
	   | None -> Evar_kinds.Define true, None
	 in
	 let tac = match Store.get ev.evar_extra evar_tactic with
	   | Some t ->
	       if Dyn.has_tag t "tactic" then
		 Some (Tacinterp.interp 
			  (Tacinterp.globTacticIn (Tacinterp.tactic_out t)))
	       else None
	   | None -> None
	 in
	 let info = { ev_name = (n, nstr);
		      ev_hyps = hyps; ev_status = status; ev_chop = chop;
		      ev_src = loc, k; ev_typ = evtyp ; ev_deps = deps; ev_tac = tac }
	 in (id, info) :: l)
      evn []
  in
  let t', _, transparent = (* Substitute evar refs in the term by variables *)
    subst_evar_constr evts 0 mkVar t 
  in
  let ty, _, _ = subst_evar_constr evts 0 mkVar ty in
  let evars = 
    List.map (fun (ev, info) ->
      let { ev_name = (_, name); ev_status = status;
	    ev_src = src; ev_typ = typ; ev_deps = deps; ev_tac = tac } = info
      in
      let status = match status with
	| Evar_kinds.Define true when Id.Set.mem name transparent ->
	  Evar_kinds.Define false
	| _ -> status
      in name, typ, src, status, deps, tac) evts
  in
  let evnames = List.map (fun (ev, info) -> ev, snd info.ev_name) evts in
  let evmap f c = pi1 (subst_evar_constr evts 0 f c) in
    Array.of_list (List.rev evars), (evnames, evmap), t', ty

let tactics_module = ["Program";"Tactics"]
let safe_init_constant md name () =
  Coqlib.check_required_library ("Coq"::md);
  Coqlib.gen_constant "Obligations" md name
let hide_obligation = safe_init_constant tactics_module "obligation"

let pperror cmd = Errors.errorlabstrm "Program" cmd
let error s = pperror (str s)

let reduce c =
  Reductionops.clos_norm_flags Closure.betaiota (Global.env ()) Evd.empty c

exception NoObligations of Id.t option

let explain_no_obligations = function
    Some ident -> str "No obligations for program " ++ str (Id.to_string ident)
  | None -> str "No obligations remaining"

type obligation_info =
    (Names.Id.t * Term.types * Evar_kinds.t Loc.located *
     Evar_kinds.obligation_definition_status * Int.Set.t * unit Proofview.tactic option) array

type 'a obligation_body = 
  | DefinedObl of 'a
  | TermObl of constr

type obligation =
  { obl_name : Id.t;
    obl_type : types;
    obl_location : Evar_kinds.t Loc.located;
    obl_body : constant obligation_body option;
    obl_status : Evar_kinds.obligation_definition_status;
    obl_deps : Int.Set.t;
    obl_tac : unit Proofview.tactic option;
  }

type obligations = (obligation array * int)

type fixpoint_kind =
  | IsFixpoint of (Id.t Loc.located option * Constrexpr.recursion_order_expr) list
  | IsCoFixpoint

type notations = (Vernacexpr.lstring * Constrexpr.constr_expr * Notation_term.scope_name option) list

type program_info = {
  prg_name: Id.t;
  prg_body: constr;
  prg_type: constr;
  prg_ctx:  Evd.evar_universe_context;
  prg_obligations: obligations;
  prg_deps : Id.t list;
  prg_fixkind : fixpoint_kind option ;
  prg_implicits : (Constrexpr.explicitation * (bool * bool * bool)) list;
  prg_notations : notations ;
  prg_kind : definition_kind;
  prg_reduce : constr -> constr;
  prg_hook : unit Lemmas.declaration_hook;
}

let assumption_message = Declare.assumption_message

let (set_default_tactic, get_default_tactic, print_default_tactic) = 
  Tactic_option.declare_tactic_option "Program tactic"

(* true = All transparent, false = Opaque if possible *)
let proofs_transparency = ref true

let set_proofs_transparency = (:=) proofs_transparency
let get_proofs_transparency () = !proofs_transparency

open Goptions

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "transparency of Program obligations";
      optkey   = ["Transparent";"Obligations"];
      optread  = get_proofs_transparency;
      optwrite = set_proofs_transparency; }

(* true = hide obligations *)
let hide_obligations = ref false

let set_hide_obligations = (:=) hide_obligations
let get_hide_obligations () = !hide_obligations

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "Hidding of Program obligations";
      optkey   = ["Hide";"Obligations"];
      optread  = get_hide_obligations;
      optwrite = set_hide_obligations; }

let shrink_obligations = ref false

let set_shrink_obligations = (:=) shrink_obligations
let get_shrink_obligations () = !shrink_obligations

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "Shrinking of Program obligations";
      optkey   = ["Shrink";"Obligations"];
      optread  = get_shrink_obligations;
      optwrite = set_shrink_obligations; }

let evar_of_obligation o = make_evar (Global.named_context_val ()) o.obl_type

let get_body obl = 
  match obl.obl_body with
  | None -> assert false
  | Some (DefinedObl c) ->
    let ctx = Environ.constant_context (Global.env ()) c in
    let pc = (c, Univ.UContext.instance ctx) in
      DefinedObl pc
  | Some (TermObl c) -> 
      TermObl c

let get_obligation_body expand obl =
  let c = get_body obl in
  let c' = 
    if expand && obl.obl_status == Evar_kinds.Expand then
      (match c with
      | DefinedObl pc -> constant_value_in (Global.env ()) pc
      | TermObl c -> c)
    else (match c with
    | DefinedObl pc -> mkConstU pc
    | TermObl c -> c)
  in c'

let obl_substitution expand obls deps =
  Int.Set.fold
    (fun x acc ->
       let xobl = obls.(x) in
       let oblb =
	 try get_obligation_body expand xobl
	 with e when Errors.noncritical e -> assert false
       in (xobl.obl_name, (xobl.obl_type, oblb)) :: acc)
    deps []

let subst_deps expand obls deps t =
  let osubst = obl_substitution expand obls deps in
    (Vars.replace_vars (List.map (fun (n, (_, b)) -> n, b) osubst) t)

let rec prod_app t n =
  match kind_of_term (strip_outer_cast t) with
    | Prod (_,_,b) -> subst1 n b
    | LetIn (_, b, t, b') -> prod_app (subst1 b b') n
    | _ ->
	errorlabstrm "prod_app"
	  (str"Needed a product, but didn't find one" ++ fnl ())


(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL

let replace_appvars subst =
  let rec aux c = 
    let f, l = decompose_app c in
      if isVar f then
	try
	  let c' = List.map (map_constr aux) l in
	  let (t, b) = Id.List.assoc (destVar f) subst in
	    mkApp (delayed_force hide_obligation, 
		   [| prod_applist t c'; applistc b c' |])
	with Not_found -> map_constr aux c
      else map_constr aux c
  in map_constr aux
       
let subst_prog expand obls ints prg =
  let subst = obl_substitution expand obls ints in
    if get_hide_obligations () then
      (replace_appvars subst prg.prg_body,
       replace_appvars subst ((* Termops.refresh_universes *) prg.prg_type))
    else 
      let subst' = List.map (fun (n, (_, b)) -> n, b) subst in
	(Vars.replace_vars subst' prg.prg_body,
	 Vars.replace_vars subst' ((* Termops.refresh_universes *) prg.prg_type))

let subst_deps_obl obls obl =
  let t' = subst_deps true obls obl.obl_deps obl.obl_type in
    { obl with obl_type = t' }

module ProgMap = Map.Make(Id)

let map_replace k v m = ProgMap.add k v (ProgMap.remove k m)

let map_keys m = ProgMap.fold (fun k _ l -> k :: l) m []

let map_cardinal m =
  let i = ref 0 in
    ProgMap.iter (fun _ _ -> incr i) m;
    !i

exception Found of program_info

let map_first m =
  try
    ProgMap.iter (fun _ v -> raise (Found v)) m;
    assert(false)
  with Found x -> x

let from_prg : program_info ProgMap.t ref =
  Summary.ref ProgMap.empty ~name:"program-tcc-table"

let close sec =
  if not (ProgMap.is_empty !from_prg) then
    let keys = map_keys !from_prg in
      errorlabstrm "Program" 
	(str "Unsolved obligations when closing " ++ str sec ++ str":" ++ spc () ++
	   prlist_with_sep spc (fun x -> Nameops.pr_id x) keys ++
	   (str (if Int.equal (List.length keys) 1 then " has " else " have ") ++
	      str "unsolved obligations"))

let input : program_info ProgMap.t -> obj =
  declare_object
    { (default_object "Program state") with
      cache_function = (fun (na, pi) -> from_prg := pi);
      load_function = (fun _ (_, pi) -> from_prg := pi);
      discharge_function = (fun _ -> close "section"; None);
      classify_function = (fun _ -> close "module"; Dispose) }
    
open Evd

let progmap_remove prg =
  Lib.add_anonymous_leaf (input (ProgMap.remove prg.prg_name !from_prg))
  
let progmap_add n prg =
  Lib.add_anonymous_leaf (input (ProgMap.add n prg !from_prg))

let progmap_replace prg' = 
  Lib.add_anonymous_leaf (input (map_replace prg'.prg_name prg' !from_prg))

let rec intset_to = function
    -1 -> Int.Set.empty
  | n -> Int.Set.add n (intset_to (pred n))

let subst_body expand prg =
  let obls, _ = prg.prg_obligations in
  let ints = intset_to (pred (Array.length obls)) in
    subst_prog expand obls ints prg

let declare_definition prg =
  let body, typ = subst_body true prg in
  let nf = Universes.nf_evars_and_universes_opt_subst (fun x -> None)
    (Evd.evar_universe_context_subst prg.prg_ctx) in
  let ce =
    definition_entry ~types:(nf typ) ~poly:(pi2 prg.prg_kind) 
      ~univs:(Evd.evar_context_universe_context prg.prg_ctx) (nf body)
  in
    progmap_remove prg;
    !declare_definition_ref prg.prg_name 
      prg.prg_kind ce prg.prg_implicits
      (Lemmas.mk_hook (fun l r ->
         Lemmas.call_hook (fun exn -> exn) prg.prg_hook l r; r))

open Pp

let rec lam_index n t acc =
  match kind_of_term t with
    | Lambda (Name n', _, _) when Id.equal n n' ->
      acc
    | Lambda (_, _, b) ->
	lam_index n b (succ acc)
    | _ -> raise Not_found

let compute_possible_guardness_evidences (n,_) fixbody fixtype =
  match n with
  | Some (loc, n) -> [lam_index n fixbody 0]
  | None ->
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
	 fixpoints ?) *)
      let m = nb_prod fixtype in
      let ctx = fst (decompose_prod_n_assum m fixtype) in
	List.map_i (fun i _ -> i) 0 ctx

let mk_proof c = ((c, Univ.ContextSet.empty), Declareops.no_seff)

let declare_mutual_definition l =
  let len = List.length l in
  let first = List.hd l in
  let fixdefs, fixtypes, fiximps =
    List.split3
      (List.map (fun x -> 
	let subs, typ = (subst_body true x) in
	let term = snd (Reductionops.splay_lam_n (Global.env ()) Evd.empty len subs) in
	let typ = snd (Reductionops.splay_prod_n (Global.env ()) Evd.empty len typ) in
	  x.prg_reduce term, x.prg_reduce typ, x.prg_implicits) l)
  in
(*   let fixdefs = List.map reduce_fix fixdefs in *)
  let fixkind = Option.get first.prg_fixkind in
  let arrrec, recvec = Array.of_list fixtypes, Array.of_list fixdefs in
  let fixdecls = (Array.of_list (List.map (fun x -> Name x.prg_name) l), arrrec, recvec) in
  let (local,poly,kind) = first.prg_kind in
  let fixnames = first.prg_deps in
  let kind = if fixkind != IsCoFixpoint then Fixpoint else CoFixpoint in
  let indexes, fixdecls =
    match fixkind with
      | IsFixpoint wfl ->
	  let possible_indexes =
	    List.map3 compute_possible_guardness_evidences
              wfl fixdefs fixtypes in
	  let indexes = 
            Pretyping.search_guard Loc.ghost (Global.env())
              possible_indexes fixdecls in
          Some indexes, 
          List.map_i (fun i _ ->
            mk_proof (mkFix ((indexes,i),fixdecls))) 0 l
      | IsCoFixpoint ->
          None,
          List.map_i (fun i _ ->
            mk_proof (mkCoFix (i,fixdecls))) 0 l
  in
  (* Declare the recursive definitions *)
  let ctx = Evd.evar_context_universe_context first.prg_ctx in
  let kns = List.map4 (!declare_fix_ref (local, poly, kind) ctx) 
    fixnames fixdecls fixtypes fiximps in
    (* Declare notations *)
    List.iter Metasyntax.add_notation_interpretation first.prg_notations;
    Declare.recursive_message (fixkind != IsCoFixpoint) indexes fixnames;
    let gr = List.hd kns in
    let kn = match gr with ConstRef kn -> kn | _ -> assert false in
      Lemmas.call_hook (fun exn -> exn) first.prg_hook local gr;
      List.iter progmap_remove l; kn

let shrink_body c = 
  let ctx, b = decompose_lam c in
  let b', n, args = 
    List.fold_left (fun (b, i, args) (n,t) ->
      if noccurn 1 b then 
	subst1 mkProp b, succ i, args
      else mkLambda (n,t,b), succ i, mkRel i :: args)
     (b, 1, []) ctx
  in List.map (fun (c,t) -> (c,None,t)) ctx, b', Array.of_list args
      
let declare_obligation prg obl body ty uctx =
  let body = prg.prg_reduce body in
  let ty = Option.map prg.prg_reduce ty in
  match obl.obl_status with
  | Evar_kinds.Expand -> { obl with obl_body = Some (TermObl body) }
  | Evar_kinds.Define opaque ->
      let opaque = if get_proofs_transparency () then false else opaque in
      let poly = pi2 prg.prg_kind in
      let ctx, body, args = 
	if get_shrink_obligations () && not poly then
	  shrink_body body else [], body, [||] 
      in
      let ce = 
        { const_entry_body = Future.from_val((body,Univ.ContextSet.empty),Declareops.no_seff);
          const_entry_secctx = None;
	  const_entry_type = if List.is_empty ctx then ty else None;
	  const_entry_polymorphic = poly;
	  const_entry_universes = uctx;
	  const_entry_opaque = opaque;
          const_entry_inline_code = false;
          const_entry_feedback = None;
      } in
    (** ppedrot: seems legit to have obligations as local *)
      let constant = Declare.declare_constant obl.obl_name ~local:true
	(DefinitionEntry ce,IsProof Property)
      in
	if not opaque then
	  Hints.add_hints false [Id.to_string prg.prg_name]
	    (Hints.HintsUnfoldEntry [EvalConstRef constant]);
	definition_message obl.obl_name;
	{ obl with obl_body = 
	    if poly then 
	      Some (DefinedObl constant)
	    else
	      Some (TermObl (it_mkLambda_or_LetIn (mkApp (mkConst constant, args)) ctx)) }

let init_prog_info n b t ctx deps fixkind notations obls impls kind reduce hook =
  let obls', b = 
    match b with
    | None ->
	assert(Int.equal (Array.length obls) 0);
	let n = Nameops.add_suffix n "_obligation" in
	  [| { obl_name = n; obl_body = None;
	       obl_location = Loc.ghost, Evar_kinds.InternalHole; obl_type = t;
	       obl_status = Evar_kinds.Expand; obl_deps = Int.Set.empty;
	       obl_tac = None } |],
	mkVar n
    | Some b ->
	Array.mapi
	  (fun i (n, t, l, o, d, tac) ->
            { obl_name = n ; obl_body = None; 
	      obl_location = l; obl_type = reduce t; obl_status = o;
	      obl_deps = d; obl_tac = tac })
	  obls, b
  in
    { prg_name = n ; prg_body = b; prg_type = reduce t; 
      prg_ctx = ctx; 
      prg_obligations = (obls', Array.length obls');
      prg_deps = deps; prg_fixkind = fixkind ; prg_notations = notations ;
      prg_implicits = impls; prg_kind = kind; prg_reduce = reduce; 
      prg_hook = hook; }

let get_prog name =
  let prg_infos = !from_prg in
    match name with
	Some n ->
	  (try ProgMap.find n prg_infos
	   with Not_found -> raise (NoObligations (Some n)))
      | None ->
	  (let n = map_cardinal prg_infos in
	     match n with
		 0 -> raise (NoObligations None)
	       | 1 -> map_first prg_infos
	       | _ -> 
                   error ("More than one program with unsolved obligations: "^
                    String.concat ", " 
                     (List.map string_of_id
                      (ProgMap.fold (fun k _ s -> k::s) prg_infos []))))

let get_any_prog () =
  let prg_infos = !from_prg in
  let n = map_cardinal prg_infos in
  if n > 0 then map_first prg_infos
  else raise (NoObligations None)

let get_prog_err n =
  try get_prog n with NoObligations id -> pperror (explain_no_obligations id)

let get_any_prog_err () =
  try get_any_prog () with NoObligations id -> pperror (explain_no_obligations id)

let obligations_solved prg = Int.equal (snd prg.prg_obligations) 0

let all_programs () =
  ProgMap.fold (fun k p l -> p :: l) !from_prg []

type progress =
    | Remain of int
    | Dependent
    | Defined of global_reference

let obligations_message rem =
  if rem > 0 then
    if Int.equal rem 1 then
      Flags.if_verbose msg_info (int rem ++ str " obligation remaining")
    else
      Flags.if_verbose msg_info (int rem ++ str " obligations remaining")
  else
    Flags.if_verbose msg_info (str "No more obligations remaining")

let update_obls prg obls rem =
  let prg' = { prg with prg_obligations = (obls, rem) } in
    progmap_replace prg';
    obligations_message rem;
    if rem > 0 then Remain rem
    else (
      match prg'.prg_deps with
      | [] ->
	  let kn = declare_definition prg' in
	    progmap_remove prg';
	    Defined kn
      | l ->
	  let progs = List.map (fun x -> ProgMap.find x !from_prg) prg'.prg_deps in
	    if List.for_all (fun x -> obligations_solved x) progs then
	      let kn = declare_mutual_definition progs in
		Defined (ConstRef kn)
	    else Dependent)

let is_defined obls x = not (Option.is_empty obls.(x).obl_body)

let deps_remaining obls deps =
  Int.Set.fold
    (fun x acc ->
      if is_defined obls x then acc
      else x :: acc)
    deps []

let dependencies obls n =
  let res = ref Int.Set.empty in
    Array.iteri
      (fun i obl ->
	if not (Int.equal i n) && Int.Set.mem n obl.obl_deps then
	  res := Int.Set.add i !res)
      obls;
    !res

let goal_kind poly = Decl_kinds.Local, poly, Decl_kinds.DefinitionBody Decl_kinds.Definition

let goal_proof_kind poly = Decl_kinds.Local, poly, Decl_kinds.Proof Decl_kinds.Lemma

let kind_of_obligation poly o =
  match o with
  | Evar_kinds.Define false | Evar_kinds.Expand -> goal_kind poly
  | _ -> goal_proof_kind poly

let not_transp_msg =
  str "Obligation should be transparent but was declared opaque." ++ spc () ++
    str"Use 'Defined' instead."

let error_not_transp () = pperror not_transp_msg

let rec string_of_list sep f = function
    [] -> ""
  | x :: [] -> f x
  | x :: ((y :: _) as tl) -> f x ^ sep ^ string_of_list sep f tl

(* Solve an obligation using tactics, return the corresponding proof term *)

let solve_by_tac name evi t poly ctx =
  let id = name in
  let concl = evi.evar_concl in
  (* spiwack: the status is dropped. *)
  let (entry,_,ctx') = Pfedit.build_constant_by_tactic 
    id ~goal_kind:(goal_kind poly) ctx evi.evar_hyps concl (Tacticals.New.tclCOMPLETE t) in
  let env = Global.env () in
  let entry = Term_typing.handle_entry_side_effects env entry in
  let body, eff = Future.force entry.Entries.const_entry_body in
  assert(Declareops.side_effects_is_empty eff);
  assert(Univ.ContextSet.is_empty (snd body));
  Inductiveops.control_only_guard (Global.env ()) (fst body);
  (fst body), entry.Entries.const_entry_type, ctx'

let rec solve_obligation prg num tac =
  let user_num = succ num in
  let obls, rem = prg.prg_obligations in
  let obl = obls.(num) in
    if not (Option.is_empty obl.obl_body) then
      pperror (str "Obligation" ++ spc () ++ int user_num ++ str "already" ++ spc() ++ str "solved.")
    else
      match deps_remaining obls obl.obl_deps with
      | [] ->
          let obl = subst_deps_obl obls obl in
          let kind = kind_of_obligation (pi2 prg.prg_kind) obl.obl_status in
            let evd = Evd.from_env ~ctx:prg.prg_ctx Environ.empty_env in
            Lemmas.start_proof_univs obl.obl_name kind evd obl.obl_type
              (fun ctx' -> Lemmas.mk_hook (fun strength gr ->
		let cst = match gr with ConstRef cst -> cst | _ -> assert false in
		let obl =
		  let transparent = evaluable_constant cst (Global.env ()) in
		  let body =
		    match obl.obl_status with
		    | Evar_kinds.Expand ->
			if not transparent then error_not_transp ()
			else DefinedObl cst
		    | Evar_kinds.Define opaque ->
			if not opaque && not transparent then error_not_transp ()
			else DefinedObl cst
		  in
		    if transparent then
		      Hints.add_hints true [Id.to_string prg.prg_name]
			(Hints.HintsUnfoldEntry [EvalConstRef cst]);
		    { obl with obl_body = Some body }
		in
		let obls = Array.copy obls in
		let _ = obls.(num) <- obl in
		let ctx' = 
		  let ctx = 
		    match ctx' with
		    | None -> prg.prg_ctx
		    | Some ctx' -> ctx'
		  in
  		    if not (pi2 prg.prg_kind) (* Not polymorphic *) then
		      (* This context is already declared globally, we cannot 
			 instantiate the rigid variables anymore *) 
		      Evd.abstract_undefined_variables ctx
		    else ctx
		in
		let res = 
		  try update_obls 
			{prg with prg_body = prg.prg_body;
			  prg_type = prg.prg_type;
			  prg_ctx = ctx' }
			  
			obls (pred rem)
		  with e when Errors.noncritical e ->
                    let e = Errors.push e in
                    pperror (Errors.iprint (Cerrors.process_vernac_interp_error e))
		in
		  match res with
		  | Remain n when n > 0 ->
		      let deps = dependencies obls num in
			if not (Int.Set.is_empty deps) then
			  ignore(auto_solve_obligations (Some prg.prg_name) None ~oblset:deps)
		  | _ -> ()));
	    trace (str "Started obligation " ++ int user_num ++ str "  proof: " ++
		     Printer.pr_constr_env (Global.env ()) Evd.empty obl.obl_type);
	    ignore (Pfedit.by (snd (get_default_tactic ())));
	    Option.iter (fun tac -> Pfedit.set_end_tac tac) tac
      | l -> pperror (str "Obligation " ++ int user_num ++ str " depends on obligation(s) "
		      ++ str (string_of_list ", " (fun x -> string_of_int (succ x)) l))

and obligation (user_num, name, typ) tac =
  let num = pred user_num in
  let prg = get_prog_err name in
  let obls, rem = prg.prg_obligations in
    if num < Array.length obls then
      let obl = obls.(num) in
	match obl.obl_body with
	    None -> solve_obligation prg num tac
	  | Some r -> error "Obligation already solved"
    else error (sprintf "Unknown obligation number %i" (succ num))


and solve_obligation_by_tac prg obls i tac =
  let obl = obls.(i) in
    match obl.obl_body with
    | Some _ -> false
    | None ->
	try
	  if List.is_empty (deps_remaining obls obl.obl_deps) then
	    let obl = subst_deps_obl obls obl in
	    let tac =
	      match tac with
	      | Some t -> t
	      | None ->
		  match obl.obl_tac with
		  | Some t -> t
		  | None -> snd (get_default_tactic ())
	    in
	    let t, ty, ctx = 
	      solve_by_tac obl.obl_name (evar_of_obligation obl) tac 
	        (pi2 !prg.prg_kind) !prg.prg_ctx
	    in
	    let uctx = Evd.evar_context_universe_context ctx in
	      prg := {!prg with prg_ctx = ctx};
	      obls.(i) <- declare_obligation !prg obl t ty uctx;
	      true
	  else false
	with e when Errors.noncritical e ->
          let (e, _) = Errors.push e in
          match e with
	  | Refiner.FailError (_, s) ->
	      user_err_loc (fst obl.obl_location, "solve_obligation", Lazy.force s)
          | e -> false

and solve_prg_obligations prg ?oblset tac =
  let obls, rem = prg.prg_obligations in
  let rem = ref rem in
  let obls' = Array.copy obls in
  let set = ref Int.Set.empty in
  let p = match oblset with
    | None -> (fun _ -> true)
    | Some s -> set := s;
      (fun i -> Int.Set.mem i !set)
  in
  let prg = ref prg in
  let _ =
    Array.iteri (fun i x ->
      if p i && solve_obligation_by_tac prg obls' i tac then
 	let deps = dependencies obls i in
 	  (set := Int.Set.union !set deps;
 	   decr rem))
      obls'
  in
    update_obls !prg obls' !rem

and solve_obligations n tac =
  let prg = get_prog_err n in
    solve_prg_obligations prg tac

and solve_all_obligations tac =
  ProgMap.iter (fun k v -> ignore(solve_prg_obligations v tac)) !from_prg

and try_solve_obligation n prg tac =
  let prg = get_prog prg in
  let obls, rem = prg.prg_obligations in
  let obls' = Array.copy obls in
  let prgref = ref prg in
    if solve_obligation_by_tac prgref obls' n tac then
      ignore(update_obls !prgref obls' (pred rem));

and try_solve_obligations n tac =
  try ignore (solve_obligations n tac) with NoObligations _ -> ()

and auto_solve_obligations n ?oblset tac : progress =
  Flags.if_verbose msg_info (str "Solving obligations automatically...");
  try solve_prg_obligations (get_prog_err n) ?oblset tac with NoObligations _ -> Dependent

open Pp
let show_obligations_of_prg ?(msg=true) prg =
  let n = prg.prg_name in
  let obls, rem = prg.prg_obligations in
  let showed = ref 5 in
    if msg then msg_info (int rem ++ str " obligation(s) remaining: ");
    Array.iteri (fun i x ->
		   match x.obl_body with
		   | None ->
		       if !showed > 0 then (
			 decr showed;
			 msg_info (str "Obligation" ++ spc() ++ int (succ i) ++ spc () ++
				   str "of" ++ spc() ++ str (Id.to_string n) ++ str ":" ++ spc () ++
				   hov 1 (Printer.pr_constr_env (Global.env ()) Evd.empty x.obl_type ++
					    str "." ++ fnl ())))
		   | Some _ -> ())
      obls

let show_obligations ?(msg=true) n =
  let progs = match n with
    | None -> all_programs ()
    | Some n ->
	try [ProgMap.find n !from_prg]
	with Not_found -> raise (NoObligations (Some n))
  in List.iter (show_obligations_of_prg ~msg) progs

let show_term n =
  let prg = get_prog_err n in
  let n = prg.prg_name in
    (str (Id.to_string n) ++ spc () ++ str":" ++ spc () ++
	     Printer.pr_constr_env (Global.env ()) Evd.empty prg.prg_type ++ spc () ++ str ":=" ++ fnl ()
	    ++ Printer.pr_constr_env (Global.env ()) Evd.empty prg.prg_body)

let add_definition n ?term t ctx ?(implicits=[]) ?(kind=Global,false,Definition) ?tactic
    ?(reduce=reduce) ?(hook=Lemmas.mk_hook (fun _ _ -> ())) obls =
  let info = str (Id.to_string n) ++ str " has type-checked" in
  let prg = init_prog_info n term t ctx [] None [] obls implicits kind reduce hook in
  let obls,_ = prg.prg_obligations in
  if Int.equal (Array.length obls) 0 then (
    Flags.if_verbose msg_info (info ++ str ".");
    let cst = declare_definition prg in
      Defined cst)
  else (
    let len = Array.length obls in
    let _ = Flags.if_verbose msg_info (info ++ str ", generating " ++ int len ++ str " obligation(s)") in
      progmap_add n prg;
      let res = auto_solve_obligations (Some n) tactic in
	match res with
	| Remain rem -> Flags.if_verbose (fun () -> show_obligations ~msg:false (Some n)) (); res
	| _ -> res)

let add_mutual_definitions l ctx ?tactic ?(kind=Global,false,Definition) ?(reduce=reduce)
    ?(hook=Lemmas.mk_hook (fun _ _ -> ())) notations fixkind =
  let deps = List.map (fun (n, b, t, imps, obls) -> n) l in
    List.iter
    (fun  (n, b, t, imps, obls) ->
     let prg = init_prog_info n (Some b) t ctx deps (Some fixkind) 
       notations obls imps kind reduce hook 
     in progmap_add n prg) l;
    let _defined =
      List.fold_left (fun finished x ->
	if finished then finished
	else
	  let res = auto_solve_obligations (Some x) tactic in
	    match res with
	    | Defined _ -> 
		(* If one definition is turned into a constant, 
		   the whole block is defined. *) true
	    | _ -> false)
	false deps
    in ()

let admit_prog prg =
  let obls, rem = prg.prg_obligations in
  let obls = Array.copy obls in
    Array.iteri 
      (fun i x ->
        match x.obl_body with
        | None ->
            let x = subst_deps_obl obls x in
	    let ctx = Evd.evar_context_universe_context prg.prg_ctx in
            let kn = Declare.declare_constant x.obl_name ~local:true
              (ParameterEntry (None,false,(x.obl_type,ctx),None), IsAssumption Conjectural)
            in
              assumption_message x.obl_name;
              obls.(i) <- { x with obl_body = Some (DefinedObl kn) }
        | Some _ -> ())
      obls;
    ignore(update_obls prg obls 0)

let rec admit_all_obligations () =
  let prg = try Some (get_any_prog ()) with NoObligations _ -> None in
  match prg with
  | None -> ()
  | Some prg ->
    admit_prog prg;
    admit_all_obligations ()

let admit_obligations n =
  match n with
  | None -> admit_all_obligations ()
  | Some _ ->
    let prg = get_prog_err n in
    admit_prog prg

let next_obligation n tac =
  let prg = match n with
  | None -> get_any_prog_err ()
  | Some _ -> get_prog_err n
  in
  let obls, rem = prg.prg_obligations in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
  | Some i -> i
  | None -> anomaly (Pp.str "Could not find a solvable obligation.")
  in
  solve_obligation prg i tac

let init_program () =
  Coqlib.check_required_library Coqlib.datatypes_module_name;
  Coqlib.check_required_library ["Coq";"Init";"Specif"];
  Coqlib.check_required_library ["Coq";"Program";"Tactics"]


let set_program_mode c =
  if c then
    if !Flags.program_mode then ()
    else begin
      init_program ();
      Flags.program_mode := true;
    end
