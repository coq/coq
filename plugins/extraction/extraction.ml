(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Util
open Names
open Term
open Vars
open Context
open Declarations
open Declareops
open Environ
open Reduction
open Reductionops
open Inductive
open Termops
open Inductiveops
open Recordops
open Namegen
open Globnames
open Miniml
open Table
open Mlutil
(*i*)

exception I of inductive_kind

(* A set of all fixpoint functions currently being extracted *)
let current_fixpoints = ref ([] : constant list)

let none = Evd.empty

let type_of env c =
  try
    let polyprop = (lang() == Haskell) in
    Retyping.get_type_of ~polyprop env none (strip_outer_cast c)
  with SingletonInductiveBecomesProp id -> error_singleton_become_prop id

let sort_of env c =
  try
    let polyprop = (lang() == Haskell) in
    Retyping.get_sort_family_of ~polyprop env none (strip_outer_cast c)
  with SingletonInductiveBecomesProp id -> error_singleton_become_prop id

(*S Generation of flags and signatures. *)

(* The type [flag] gives us information about any Coq term:
   \begin{itemize}
   \item [TypeScheme] denotes a type scheme, that is
     something that will become a type after enough applications.
     More formally, a type scheme has type $(x_1:X_1)\ldots(x_n:X_n)s$ with
     [s = Set], [Prop] or [Type]
   \item [Default] denotes the other cases. It may be inexact after
     instantiation. For example [(X:Type)X] is [Default] and may give [Set]
     after instantiation, which is rather [TypeScheme]
   \item [Logic] denotes a term of sort [Prop], or a type scheme on sort [Prop]
   \item [Info] is the opposite. The same example [(X:Type)X] shows
     that an [Info] term might in fact be [Logic] later on.
   \end{itemize} *)

type info = Logic | Info

type scheme = TypeScheme | Default

type flag = info * scheme

(*s [flag_of_type] transforms a type [t] into a [flag].
  Really important function. *)

let rec flag_of_type env t : flag =
  let t = whd_betadeltaiota env none t in
  match kind_of_term t with
    | Prod (x,t,c) -> flag_of_type (push_rel (x,None,t) env) c
    | Sort s when Sorts.is_prop s -> (Logic,TypeScheme)
    | Sort _ -> (Info,TypeScheme)
    | _ -> if (sort_of env t) == InProp then (Logic,Default) else (Info,Default)

(*s Two particular cases of [flag_of_type]. *)

let is_default env t = match flag_of_type env t with
| (Info, Default) -> true
| _ -> false

exception NotDefault of kill_reason

let check_default env t =
  match flag_of_type env t with
    | _,TypeScheme -> raise (NotDefault Ktype)
    | Logic,_ -> raise (NotDefault Kother)
    | _ -> ()

let is_info_scheme env t = match flag_of_type env t with
| (Info, TypeScheme) -> true
| _ -> false

(*s [type_sign] gernerates a signature aimed at treating a type application. *)

let rec type_sign env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) ->
	(if is_info_scheme env t then Keep else Kill Kother)
	:: (type_sign (push_rel_assum (n,t) env) d)
    | _ -> []

let rec type_scheme_nb_args env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) ->
	let n = type_scheme_nb_args (push_rel_assum (n,t) env) d in
	if is_info_scheme env t then n+1 else n
    | _ -> 0

let _ = Hook.set type_scheme_nb_args_hook type_scheme_nb_args

(*s [type_sign_vl] does the same, plus a type var list. *)

(* When generating type variables, we avoid any ' in their names
   (otherwise this may cause a lexer conflict in ocaml with 'a').
   We also get rid of unicode characters. Anyway, since type variables
   are local, the created name is just a matter of taste...
   See also Bug #3227 *)

let make_typvar n vl =
  let id = id_of_name n in
  let id' =
    let s = Id.to_string id in
    if not (String.contains s '\'') && Unicode.is_basic_ascii s then id
    else id_of_name Anonymous
  in
  next_ident_away id' vl

let rec type_sign_vl env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) ->
	let s,vl = type_sign_vl (push_rel_assum (n,t) env) d in
	if not (is_info_scheme env t) then Kill Kother::s, vl
	else Keep::s, (make_typvar n vl) :: vl
    | _ -> [],[]

let rec nb_default_params env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) ->
	let n = nb_default_params (push_rel_assum (n,t) env) d in
	if is_default env t then n+1 else n
    | _ -> 0

(* Enriching a signature with implicit information *)

let sign_with_implicits r s nb_params =
  let implicits = implicits_of_global r in
  let rec add_impl i = function
    | [] -> []
    | sign::s ->
	let sign' =
	  if sign == Keep && Int.List.mem i implicits
          then Kill Kother else sign
	in sign' :: add_impl (succ i) s
  in
  add_impl (1+nb_params) s

(* Enriching a exception message *)

let rec handle_exn r n fn_name = function
  | MLexn s ->
      (try Scanf.sscanf s "UNBOUND %d%!"
	 (fun i ->
	    assert ((0 < i) && (i <= n));
	    MLexn ("IMPLICIT "^ msg_non_implicit r (n+1-i) (fn_name i)))
       with Scanf.Scan_failure _ | End_of_file -> MLexn s)
  | a -> ast_map (handle_exn r n fn_name) a

(*S Management of type variable contexts. *)

(* A De Bruijn variable context (db) is a context for translating Coq [Rel]
   into ML type [Tvar]. *)

(*s From a type signature toward a type variable context (db). *)

let db_from_sign s =
  let rec make i acc = function
    | [] -> acc
    | Keep :: l -> make (i+1) (i::acc) l
    | Kill _ :: l -> make i (0::acc) l
  in make 1 [] s

(*s Create a type variable context from indications taken from
  an inductive type (see just below). *)

let rec db_from_ind dbmap i =
  if Int.equal i 0 then []
  else (try Int.Map.find i dbmap with Not_found -> 0)::(db_from_ind dbmap (i-1))

(*s [parse_ind_args] builds a map: [i->j] iff the i-th Coq argument
  of a constructor corresponds to the j-th type var of the ML inductive. *)

(* \begin{itemize}
   \item [si] : signature of the inductive
   \item [i] :  counter of Coq args for [(I args)]
   \item [j] : counter of ML type vars
   \item [relmax] : total args number of the constructor
   \end{itemize} *)

let parse_ind_args si args relmax =
  let rec parse i j = function
    | [] -> Int.Map.empty
    | Kill _ :: s -> parse (i+1) j s
    | Keep :: s ->
      (match kind_of_term args.(i-1) with
	 | Rel k -> Int.Map.add (relmax+1-k) j (parse (i+1) (j+1) s)
	 | _ -> parse (i+1) (j+1) s)
  in parse 1 1 si

let oib_equal o1 o2 =
  Id.equal o1.mind_typename o2.mind_typename &&
  List.equal eq_rel_declaration o1.mind_arity_ctxt o2.mind_arity_ctxt &&
    begin
      match o1.mind_arity, o2.mind_arity with
      | RegularArity {mind_user_arity=c1; mind_sort=s1}, RegularArity {mind_user_arity=c2; mind_sort=s2} ->
	eq_constr c1 c2 && Sorts.equal s1 s2
      | TemplateArity p1, TemplateArity p2 ->
	let eq o1 o2 = Option.equal Univ.Level.equal o1 o2 in
	  List.equal eq p1.template_param_levels p2.template_param_levels &&
	    Univ.Universe.equal p1.template_level p2.template_level
      | _, _ -> false
    end &&
    Array.equal Id.equal o1.mind_consnames o2.mind_consnames

let eq_record x y =
  Option.equal (Option.equal (fun (_, x, y) (_, x', y') -> Array.for_all2 eq_constant x x')) x y

let mib_equal m1 m2 =
  Array.equal oib_equal m1.mind_packets m1.mind_packets &&
  eq_record m1.mind_record m2.mind_record &&
  (m1.mind_finite : Decl_kinds.recursivity_kind) == m2.mind_finite &&
  Int.equal m1.mind_ntypes m2.mind_ntypes &&
  List.equal eq_named_declaration m1.mind_hyps m2.mind_hyps &&
  Int.equal m1.mind_nparams m2.mind_nparams &&
  Int.equal m1.mind_nparams_rec m2.mind_nparams_rec &&
  List.equal eq_rel_declaration m1.mind_params_ctxt m2.mind_params_ctxt &&
  (* Univ.UContext.eq *) m1.mind_universes == m2.mind_universes (** FIXME *)
  (* m1.mind_universes = m2.mind_universes *)

(*S Extraction of a type. *)

(* [extract_type env db c args] is used to produce an ML type from the
   coq term [(c args)], which is supposed to be a Coq type. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

(* [j] stands for the next ML type var. [j=0] means we do not
   generate ML type var anymore (in subterms for example). *)


let rec extract_type env db j c args =
  match kind_of_term (whd_betaiotazeta Evd.empty c) with
    | App (d, args') ->
	(* We just accumulate the arguments. *)
	extract_type env db j d (Array.to_list args' @ args)
    | Lambda (_,_,d) ->
	(match args with
	   | [] -> assert false (* A lambda cannot be a type. *)
	   | a :: args -> extract_type env db j (subst1 a d) args)
    | Prod (n,t,d) ->
	assert (List.is_empty args);
	let env' = push_rel_assum (n,t) env in
	(match flag_of_type env t with
	   | (Info, Default) ->
	       (* Standard case: two [extract_type] ... *)
	       let mld = extract_type env' (0::db) j d [] in
	       (match expand env mld with
		  | Tdummy d -> Tdummy d
		  | _ -> Tarr (extract_type env db 0 t [], mld))
	   | (Info, TypeScheme) when j > 0 ->
	       (* A new type var. *)
	       let mld = extract_type env' (j::db) (j+1) d [] in
	       (match expand env mld with
		  | Tdummy d -> Tdummy d
		  | _ -> Tarr (Tdummy Ktype, mld))
	   | _,lvl ->
	       let mld = extract_type env' (0::db) j d [] in
	       (match expand env mld with
		  | Tdummy d -> Tdummy d
		  | _ ->
		      let reason = if lvl == TypeScheme then Ktype else Kother in
		      Tarr (Tdummy reason, mld)))
    | Sort _ -> Tdummy Ktype (* The two logical cases. *)
    | _ when sort_of env (applist (c, args)) == InProp -> Tdummy Kother
    | Rel n ->
	(match lookup_rel n env with
           | (_,Some t,_) -> extract_type env db j (lift n t) args
	   | _ ->
	       (* Asks [db] a translation for [n]. *)
	       if n > List.length db then Tunknown
	       else let n' = List.nth db (n-1) in
	       if Int.equal n' 0 then Tunknown else Tvar n')
    | Const (kn,u as c) ->
	let r = ConstRef kn in
	let cb = lookup_constant kn env in
	let typ,_ = Typeops.type_of_constant env c in
	(match flag_of_type env typ with
	   | (Logic,_) -> assert false (* Cf. logical cases above *)
	   | (Info, TypeScheme) ->
	       let mlt = extract_type_app env db (r, type_sign env typ) args in
	       (match cb.const_body with
		  | Undef _ | OpaqueDef _ -> mlt
		  | Def _ when is_custom r -> mlt
		  | Def lbody ->
		      let newc = applist (Mod_subst.force_constr lbody, args) in
		      let mlt' = extract_type env db j newc [] in
		      (* ML type abbreviations interact badly with Coq *)
		      (* reduction, so [mlt] and [mlt'] might be different: *)
		      (* The more precise is [mlt'], extracted after reduction *)
		      (* The shortest is [mlt], which use abbreviations *)
		      (* If possible, we take [mlt], otherwise [mlt']. *)
		      if eq_ml_type (expand env mlt) (expand env mlt') then mlt else mlt')
	   | (Info, Default) ->
               (* Not an ML type, for example [(c:forall X, X->X) Type nat] *)
	       (match cb.const_body with
		  | Undef _  | OpaqueDef _ -> Tunknown (* Brutal approx ... *)
		  | Def lbody ->
		      (* We try to reduce. *)
		      let newc = applist (Mod_subst.force_constr lbody, args) in
		      extract_type env db j newc []))
    | Ind ((kn,i),u) ->
	let s = (extract_ind env kn).ind_packets.(i).ip_sign in
	extract_type_app env db (IndRef (kn,i),s) args
    | Case _ | Fix _ | CoFix _ -> Tunknown
    | _ -> assert false

(*s Auxiliary function dealing with type application.
  Precondition: [r] is a type scheme represented by the signature [s],
  and is completely applied: [List.length args = List.length s]. *)

and extract_type_app env db (r,s) args =
  let ml_args =
    List.fold_right
      (fun (b,c) a -> if b == Keep then
	 let p = List.length (fst (splay_prod env none (type_of env c))) in
         let db = iterate (fun l -> 0 :: l) p db in
         (extract_type_scheme env db c p) :: a
       else a)
      (List.combine s args) []
  in Tglob (r,  ml_args)

(*S Extraction of a type scheme. *)

(* [extract_type_scheme env db c p] works on a Coq term [c] which is
  an informative type scheme. It means that [c] is not a Coq type, but will
  be when applied to sufficiently many arguments ([p] in fact).
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

and extract_type_scheme env db c p =
  if Int.equal p 0 then extract_type env db 0 c []
  else
    let c = whd_betaiotazeta Evd.empty c in
    match kind_of_term c with
      | Lambda (n,t,d) ->
          extract_type_scheme (push_rel_assum (n,t) env) db d (p-1)
      | _ ->
          let rels = fst (splay_prod env none (type_of env c)) in
          let env = push_rels_assum rels env in
          let eta_args = List.rev_map mkRel (List.interval 1 p) in
          extract_type env db 0 (lift p c) eta_args


(*S Extraction of an inductive type. *)

and extract_ind env kn = (* kn is supposed to be in long form *)
  let mib = Environ.lookup_mind kn env in
  try
    (* For a same kn, we can get various bodies due to module substitutions.
       We hence check that the mib has not changed from recording
       time to retrieving time. Ideally we should also check the env. *)
    let (mib0,ml_ind) = lookup_ind kn in
    if not (mib_equal mib mib0) then raise Not_found;
    ml_ind
  with Not_found ->
    (* First, if this inductive is aliased via a Module,
       we process the original inductive if possible.
       When at toplevel of the monolithic case, we cannot do much
       (cf Vector and bug #2570) *)
    let equiv =
      if lang () != Ocaml ||
	 (not (modular ()) && at_toplevel (mind_modpath kn)) ||
	 KerName.equal (canonical_mind kn) (user_mind kn)
      then
	NoEquiv
      else
	begin
	  ignore (extract_ind env (mind_of_kn (canonical_mind kn)));
	  Equiv (canonical_mind kn)
	end
    in
    (* Everything concerning parameters. *)
    (* We do that first, since they are common to all the [mib]. *)
    let mip0 = mib.mind_packets.(0) in
    let npar = mib.mind_nparams in
    let epar = push_rel_context mib.mind_params_ctxt env in
    (* First pass: we store inductive signatures together with *)
    (* their type var list. *)
    let packets =
      Array.mapi
	(fun i mip ->
	   let (ind,u), ctx = 
	     Universes.fresh_inductive_instance env (kn,i) in
	   let ar = Inductive.type_of_inductive env ((mib,mip),u) in
	   let info = (fst (flag_of_type env ar) = Info) in
	   let s,v = if info then type_sign_vl env ar else [],[] in
	   let t = Array.make (Array.length mip.mind_nf_lc) [] in
	   { ip_typename = mip.mind_typename;
	     ip_consnames = mip.mind_consnames;
	     ip_logical = not info;
	     ip_sign = s;
	     ip_vars = v;
	     ip_types = t }, u)
	mib.mind_packets
    in

    add_ind kn mib
      {ind_kind = Standard;
       ind_nparams = npar;
       ind_packets = Array.map fst packets;
       ind_equiv = equiv
      };
    (* Second pass: we extract constructors *)
    for i = 0 to mib.mind_ntypes - 1 do
      let p,u = packets.(i) in
      if not p.ip_logical then
	let types = arities_of_constructors env ((kn,i),u) in
	for j = 0 to Array.length types - 1 do
	  let t = snd (decompose_prod_n npar types.(j)) in
	  let prods,head = dest_prod epar t in
	  let nprods = List.length prods in
          let args = match kind_of_term head with
            | App (f,args) -> args (* [kind_of_term f = Ind ip] *)
            | _ -> [||]
          in
	  let dbmap = parse_ind_args p.ip_sign args (nprods + npar) in
	  let db = db_from_ind dbmap npar in
	  p.ip_types.(j) <- extract_type_cons epar db dbmap t (npar+1)
	done
    done;
    (* Third pass: we determine special cases. *)
    let ind_info =
      try
	let ip = (kn, 0) in
	let r = IndRef ip in
	if is_custom r then raise (I Standard);
	if mib.mind_finite == Decl_kinds.CoFinite then raise (I Coinductive);
	if not (Int.equal mib.mind_ntypes 1) then raise (I Standard);
	let p,u = packets.(0) in
	if p.ip_logical then raise (I Standard);
	if not (Int.equal (Array.length p.ip_types) 1) then raise (I Standard);
	let typ = p.ip_types.(0) in
	let l = List.filter (fun t -> not (isDummy (expand env t))) typ in
	if not (keep_singleton ()) &&
	    Int.equal (List.length l) 1 && not (type_mem_kn kn (List.hd l))
	then raise (I Singleton);
	if List.is_empty l then raise (I Standard);
	if Option.is_empty mib.mind_record then raise (I Standard);
	(* Now we're sure it's a record. *)
	(* First, we find its field names. *)
	let rec names_prod t = match kind_of_term t with
	  | Prod(n,_,t) -> n::(names_prod t)
	  | LetIn(_,_,_,t) -> names_prod t
	  | Cast(t,_,_) -> names_prod t
	  | _ -> []
	in
	let field_names =
	  List.skipn mib.mind_nparams (names_prod mip0.mind_user_lc.(0)) in
	assert (Int.equal (List.length field_names) (List.length typ));
	let projs = ref Cset.empty in
	let mp = MutInd.modpath kn in
	let rec select_fields l typs = match l,typs with
	  | [],[] -> []
	  | _::l, typ::typs when isDummy (expand env typ) ->
	      select_fields l typs
	  | Anonymous::l, typ::typs ->
	      None :: (select_fields l typs)
	  | Name id::l, typ::typs ->
	      let knp = Constant.make2 mp (Label.of_id id) in
	      (* Is it safe to use [id] for projections [foo.id] ? *)
	      if List.for_all ((==) Keep) (type2signature env typ)
	      then projs := Cset.add knp !projs;
	      Some (ConstRef knp) :: (select_fields l typs)
	  | _ -> assert false
	in
	let field_glob = select_fields field_names typ
	in
	(* Is this record officially declared with its projections ? *)
	(* If so, we use this information. *)
	begin try
	  let n = nb_default_params env
            (Inductive.type_of_inductive env ((mib,mip0),u))
	  in
	  let check_proj kn = if Cset.mem kn !projs then add_projection n kn ip
          in
	  List.iter (Option.iter check_proj) (lookup_projections ip)
	with Not_found -> ()
	end;
	Record field_glob
      with (I info) -> info
    in
    let i = {ind_kind = ind_info;
	     ind_nparams = npar;
	     ind_packets = Array.map fst packets;
	     ind_equiv = equiv }
    in
    add_ind kn mib i;
    add_inductive_kind kn i.ind_kind;
    i

(*s [extract_type_cons] extracts the type of an inductive
  constructor toward the corresponding list of ML types.

   - [db] is a context for translating Coq [Rel] into ML type [Tvar]
   - [dbmap] is a translation map (produced by a call to [parse_in_args])
   - [i] is the rank of the current product (initially [params_nb+1])
*)

and extract_type_cons env db dbmap c i =
  match kind_of_term (whd_betadeltaiota env none c) with
    | Prod (n,t,d) ->
	let env' = push_rel_assum (n,t) env in
	let db' = (try Int.Map.find i dbmap with Not_found -> 0) :: db in
	let l = extract_type_cons env' db' dbmap d (i+1) in
	(extract_type env db 0 t []) :: l
    | _ -> []

(*s Recording the ML type abbreviation of a Coq type scheme constant. *)

and mlt_env env r = match r with
  | ConstRef kn ->
      (try
	 if not (visible_con kn) then raise Not_found;
	 match lookup_term kn with
	   | Dtype (_,vl,mlt) -> Some mlt
	   | _ -> None
       with Not_found ->
	 let cb = Environ.lookup_constant kn env in
	 let typ = Typeops.type_of_constant_type env cb.const_type
 (* FIXME not sure if we should instantiate univs here *) in
	 match cb.const_body with
	   | Undef _ | OpaqueDef _ -> None
	   | Def l_body ->
	       (match flag_of_type env typ with
		  | Info,TypeScheme ->
		      let body = Mod_subst.force_constr l_body in
		      let s,vl = type_sign_vl env typ in
		      let db = db_from_sign s in
		      let t = extract_type_scheme env db body (List.length s)
		      in add_term kn (Dtype (r, vl, t)); Some t
		  | _ -> None))
  | _ -> None

and expand env = type_expand (mlt_env env)
and type2signature env = type_to_signature (mlt_env env)
let type2sign env = type_to_sign (mlt_env env)
let type_expunge env = type_expunge (mlt_env env)
let type_expunge_from_sign env = type_expunge_from_sign (mlt_env env)

(*s Extraction of the type of a constant. *)

let record_constant_type env kn opt_typ =
  try
    if not (visible_con kn) then raise Not_found;
    lookup_type kn
  with Not_found ->
    let typ = match opt_typ with
      | None -> Typeops.type_of_constant_type env (lookup_constant kn env).const_type
      | Some typ -> typ
    in let mlt = extract_type env [] 1 typ []
    in let schema = (type_maxvar mlt, mlt)
    in add_type kn schema; schema

(*S Extraction of a term. *)

(* Precondition: [(c args)] is not a type scheme, and is informative. *)

(* [mle] is a ML environment [Mlenv.t]. *)
(* [mlt] is the ML type we want our extraction of [(c args)] to have. *)

let rec extract_term env mle mlt c args =
  match kind_of_term c with
    | App (f,a) ->
	extract_term env mle mlt f (Array.to_list a @ args)
    | Lambda (n, t, d) ->
	let id = id_of_name n in
	(match args with
	   | a :: l ->
	       (* We make as many [LetIn] as possible. *)
 	       let d' = mkLetIn (Name id,a,t,applistc d (List.map (lift 1) l))
	       in extract_term env mle mlt d' []
	   | [] ->
	       let env' = push_rel_assum (Name id, t) env in
	       let id, a =
		 try check_default env t; Id id, new_meta()
		 with NotDefault d -> Dummy, Tdummy d
	       in
	       let b = new_meta () in
	       (* If [mlt] cannot be unified with an arrow type, then magic! *)
	       let magic = needs_magic (mlt, Tarr (a, b)) in
	       let d' = extract_term env' (Mlenv.push_type mle a) b d [] in
	       put_magic_if magic (MLlam (id, d')))
    | LetIn (n, c1, t1, c2) ->
	let id = id_of_name n in
	let env' = push_rel (Name id, Some c1, t1) env in
	(* We directly push the args inside the [LetIn].
           TODO: the opt_let_app flag is supposed to prevent that *)
	let args' = List.map (lift 1) args in
	(try
	  check_default env t1;
	  let a = new_meta () in
	  let c1' = extract_term env mle a c1 [] in
	  (* The type of [c1'] is generalized and stored in [mle]. *)
	  let mle' =
	    if generalizable c1'
	    then Mlenv.push_gen mle a
	    else Mlenv.push_type mle a
	  in
	  MLletin (Id id, c1', extract_term env' mle' mlt c2 args')
	with NotDefault d ->
	  let mle' = Mlenv.push_std_type mle (Tdummy d) in
	  ast_pop (extract_term env' mle' mlt c2 args'))
    | Const (kn,u) ->
	extract_cst_app env mle mlt kn u args
    | Construct (cp,u) ->
	extract_cons_app env mle mlt cp u args
    | Proj (p, c) ->
        extract_cst_app env mle mlt (Projection.constant p) Univ.Instance.empty (c :: args)
    | Rel n ->
	(* As soon as the expected [mlt] for the head is known, *)
	(* we unify it with an fresh copy of the stored type of [Rel n]. *)
	let extract_rel mlt = put_magic (mlt, Mlenv.get mle n) (MLrel n)
	in extract_app env mle mlt extract_rel args
    | Case ({ci_ind=ip},_,c0,br) ->
 	extract_app env mle mlt (extract_case env mle (ip,c0,br)) args
    | Fix ((_,i),recd) ->
 	extract_app env mle mlt (extract_fix env mle i recd) args
    | CoFix (i,recd) ->
 	extract_app env mle mlt (extract_fix env mle i recd) args
    | Cast (c,_,_) -> extract_term env mle mlt c args
    | Ind _ | Prod _ | Sort _ | Meta _ | Evar _ | Var _ -> assert false

(*s [extract_maybe_term] is [extract_term] for usual terms, else [MLdummy] *)

and extract_maybe_term env mle mlt c =
  try check_default env (type_of env c);
    extract_term env mle mlt c []
  with NotDefault d ->
    put_magic (mlt, Tdummy d) MLdummy

(*s Generic way to deal with an application. *)

(* We first type all arguments starting with unknown meta types.
   This gives us the expected type of the head. Then we use the
   [mk_head] to produce the ML head from this type. *)

and extract_app env mle mlt mk_head args =
  let metas = List.map new_meta args in
  let type_head = type_recomp (metas, mlt) in
  let mlargs = List.map2 (extract_maybe_term env mle) metas args in
  mlapp (mk_head type_head) mlargs

(*s Auxiliary function used to extract arguments of constant or constructor. *)

and make_mlargs env e s args typs =
  let rec f = function
    | [], [], _ -> []
    | a::la, t::lt, [] -> extract_maybe_term env e t a :: (f (la,lt,[]))
    | a::la, t::lt, Keep::s -> extract_maybe_term env e t a :: (f (la,lt,s))
    | _::la, _::lt, _::s -> f (la,lt,s)
    | _ -> assert false
  in f (args,typs,s)

(*s Extraction of a constant applied to arguments. *)

and extract_cst_app env mle mlt kn u args =
  (* First, the [ml_schema] of the constant, in expanded version. *)
  let nb,t = record_constant_type env kn None in
  let schema = nb, expand env t in
  (* Can we instantiate types variables for this constant ? *)
  (* In Ocaml, inside the definition of this constant, the answer is no. *)
  let instantiated =
    if lang () == Ocaml && List.mem_f Constant.equal kn !current_fixpoints
    then var2var' (snd schema)
    else instantiation schema
  in
  (* Then the expected type of this constant. *)
  let a = new_meta () in
  (* We compare stored and expected types in two steps. *)
  (* First, can [kn] be applied to all args ? *)
  let metas = List.map new_meta args in
  let magic1 = needs_magic (type_recomp (metas, a), instantiated) in
  (* Second, is the resulting type compatible with the expected type [mlt] ? *)
  let magic2 = needs_magic (a, mlt) in
  (* The internal head receives a magic if [magic1] *)
  let head = put_magic_if magic1 (MLglob (ConstRef kn)) in
  (* Now, the extraction of the arguments. *)
  let s_full = type2signature env (snd schema) in
  let s_full = sign_with_implicits (ConstRef kn) s_full 0 in
  let s = sign_no_final_keeps s_full in
  let ls = List.length s in
  let la = List.length args in
  (* The ml arguments, already expunged from known logical ones *)
  let mla = make_mlargs env mle s args metas in
  let mla =
    if magic1 || lang () != Ocaml then mla
    else
      try
        (* for better optimisations later, we discard dependent args
           of projections and replace them by fake args that will be
           removed during final pretty-print. *)
	let l,l' = List.chop (projection_arity (ConstRef kn)) mla in
	if not (List.is_empty l') then (List.map (fun _ -> MLexn "Proj Args") l) @ l'
	else mla
      with e when Errors.noncritical e -> mla
  in
  (* For strict languages, purely logical signatures with at least
     one [Kill Kother] lead to a dummy lam. So a [MLdummy] is left
     accordingly. *)
  let optdummy = match sign_kind s_full with
    | UnsafeLogicalSig when lang () != Haskell -> [MLdummy]
    | _ -> []
  in
  (* Different situations depending of the number of arguments: *)
  if la >= ls
  then
    (* Enough args, cleanup already done in [mla], we only add the
       additionnal dummy if needed. *)
    put_magic_if (magic2 && not magic1) (mlapp head (optdummy @ mla))
  else
    (* Partially applied function with some logical arg missing.
       We complete via eta and expunge logical args. *)
    let ls' = ls-la in
    let s' = List.skipn la s in
    let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
    let e = anonym_or_dummy_lams (mlapp head mla) s' in
    put_magic_if magic2 (remove_n_lams (List.length optdummy) e)

(*s Extraction of an inductive constructor applied to arguments. *)

(* \begin{itemize}
   \item In ML, contructor arguments are uncurryfied.
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Coq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize} *)

and extract_cons_app env mle mlt (((kn,i) as ip,j) as cp) u args =
  (* First, we build the type of the constructor, stored in small pieces. *)
  let mi = extract_ind env kn in
  let params_nb = mi.ind_nparams in
  let oi = mi.ind_packets.(i) in
  let nb_tvars = List.length oi.ip_vars
  and types = List.map (expand env) oi.ip_types.(j-1) in
  let list_tvar = List.map (fun i -> Tvar i) (List.interval 1 nb_tvars) in
  let type_cons = type_recomp (types, Tglob (IndRef ip, list_tvar)) in
  let type_cons = instantiation (nb_tvars, type_cons) in
  (* Then, the usual variables [s], [ls], [la], ... *)
  let s = List.map (type2sign env) types in
  let s = sign_with_implicits (ConstructRef cp) s params_nb in
  let ls = List.length s in
  let la = List.length args in
  assert (la <= ls + params_nb);
  let la' = max 0 (la - params_nb) in
  let args' = List.lastn la' args in
  (* Now, we build the expected type of the constructor *)
  let metas = List.map new_meta args' in
  (* If stored and expected types differ, then magic! *)
  let a = new_meta () in
  let magic1 = needs_magic (type_cons, type_recomp (metas, a)) in
  let magic2 = needs_magic (a, mlt) in
  let head mla =
    if mi.ind_kind == Singleton then
      put_magic_if magic1 (List.hd mla) (* assert (List.length mla = 1) *)
    else
      let typeargs = match snd (type_decomp type_cons) with
	| Tglob (_,l) -> List.map type_simpl l
	| _ -> assert false
      in
      let typ = Tglob(IndRef ip, typeargs) in
      put_magic_if magic1 (MLcons (typ, ConstructRef cp, mla))
  in
  (* Different situations depending of the number of arguments: *)
  if la < params_nb then
    let head' = head (eta_args_sign ls s) in
    put_magic_if magic2
      (dummy_lams (anonym_or_dummy_lams head' s) (params_nb - la))
  else
    let mla = make_mlargs env mle s args' metas in
    if Int.equal la (ls + params_nb)
    then put_magic_if (magic2 && not magic1) (head mla)
    else (* [ params_nb <= la <= ls + params_nb ] *)
      let ls' = params_nb + ls - la in
      let s' = List.lastn ls' s in
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      put_magic_if magic2 (anonym_or_dummy_lams (head mla) s')

(*S Extraction of a case. *)

and extract_case env mle ((kn,i) as ip,c,br) mlt =
  (* [br]: bodies of each branch (in functional form) *)
  (* [ni]: number of arguments without parameters in each branch *)
  let ni = constructors_nrealargs_env env ip in
  let br_size = Array.length br in
  assert (Int.equal (Array.length ni) br_size);
  if Int.equal br_size 0 then begin
    add_recursors env kn; (* May have passed unseen if logical ... *)
    MLexn "absurd case"
  end else
    (* [c] has an inductive type, and is not a type scheme type. *)
    let t = type_of env c in
    (* The only non-informative case: [c] is of sort [Prop] *)
    if (sort_of env t) == InProp then
      begin
	add_recursors env kn; (* May have passed unseen if logical ... *)
	(* Logical singleton case: *)
	(* [match c with C i j k -> t] becomes [t'] *)
	assert (Int.equal br_size 1);
	let s = iterate (fun l -> Kill Kother :: l) ni.(0) [] in
	let mlt = iterate (fun t -> Tarr (Tdummy Kother, t)) ni.(0) mlt in
	let e = extract_maybe_term env mle mlt br.(0) in
	snd (case_expunge s e)
      end
    else
      let mi = extract_ind env kn in
      let oi = mi.ind_packets.(i) in
      let metas = Array.init (List.length oi.ip_vars) new_meta in
      (* The extraction of the head. *)
      let type_head = Tglob (IndRef ip, Array.to_list metas) in
      let a = extract_term env mle type_head c [] in
      (* The extraction of each branch. *)
      let extract_branch i =
	let r = ConstructRef (ip,i+1) in
	(* The types of the arguments of the corresponding constructor. *)
	let f t = type_subst_vect metas (expand env t) in
	let l = List.map f oi.ip_types.(i) in
	(* the corresponding signature *)
	let s = List.map (type2sign env) oi.ip_types.(i) in
	let s = sign_with_implicits r s mi.ind_nparams in
	(* Extraction of the branch (in functional form). *)
	let e = extract_maybe_term env mle (type_recomp (l,mlt)) br.(i) in
	(* We suppress dummy arguments according to signature. *)
	let ids,e = case_expunge s e in
	let e' = handle_exn r (List.length s) (fun _ -> Anonymous) e in
	(List.rev ids, Pusual r, e')
      in
      if mi.ind_kind == Singleton then
	begin
	  (* Informative singleton case: *)
	  (* [match c with C i -> t] becomes [let i = c' in t'] *)
	  assert (Int.equal br_size 1);
	  let (ids,_,e') = extract_branch 0 in
	  assert (Int.equal (List.length ids) 1);
	  MLletin (tmp_id (List.hd ids),a,e')
	end
      else
	(* Standard case: we apply [extract_branch]. *)
	let typs = List.map type_simpl (Array.to_list metas) in
	let typ = Tglob (IndRef ip,typs) in
	MLcase (typ, a, Array.init br_size extract_branch)

(*s Extraction of a (co)-fixpoint. *)

and extract_fix env mle i (fi,ti,ci as recd) mlt =
  let env = push_rec_types recd env in
  let metas = Array.map new_meta fi in
  metas.(i) <- mlt;
  let mle = Array.fold_left Mlenv.push_type mle metas in
  let ei = Array.map2 (extract_maybe_term env mle) metas ci in
  MLfix (i, Array.map id_of_name fi, ei)

(*S ML declarations. *)

(* [decomp_lams_eta env c t] finds the number [n] of products in the type [t],
   and decompose the term [c] in [n] lambdas, with eta-expansion if needed. *)

let decomp_lams_eta_n n m env c t =
  let rels = fst (splay_prod_n env none n t) in
  let rels = List.map (fun (id,_,c) -> (id,c)) rels in
  let rels',c = decompose_lam c in
  let d = n - m in
  (* we'd better keep rels' as long as possible. *)
  let rels = (List.firstn d rels) @ rels' in
  let eta_args = List.rev_map mkRel (List.interval 1 d) in
  rels, applist (lift d c,eta_args)

(* Let's try to identify some situation where extracted code
   will allow generalisation of type variables *)

let rec gentypvar_ok c = match kind_of_term c with
  | Lambda _ | Const _ -> true
  | App (c,v) ->
      (* if all arguments are variables, these variables will
	 disappear after extraction (see [empty_s] below) *)
      Array.for_all isRel v && gentypvar_ok c
  | Cast (c,_,_) -> gentypvar_ok c
  | _ -> false

(*s From a constant to a ML declaration. *)

let extract_std_constant env kn body typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = snd (record_constant_type env kn (Some typ)) in
  (* The real type [t']: without head products, expanded, *)
  (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
  let l,t' = type_decomp (expand env (var2var' t)) in
  let s = List.map (type2sign env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits (ConstRef kn) s 0 in
  (* Decomposing the top level lambdas of [body].
     If there isn't enough, it's ok, as long as remaining args
     aren't to be pruned (and initial lambdas aren't to be all
     removed if the target language is strict). In other situations,
     eta-expansions create artificially enough lams (but that may
     break user's clever let-ins and partial applications). *)
  let rels, c =
    let n = List.length s
    and m = nb_lam body in
    if n <= m then decompose_lam_n n body
    else
      let s,s' = List.chop m s in
      if List.for_all ((==) Keep) s' &&
	(lang () == Haskell || sign_kind s != UnsafeLogicalSig)
      then decompose_lam_n m body
      else decomp_lams_eta_n n m env body typ
  in
  (* Should we do one eta-expansion to avoid non-generalizable '_a ? *)
  let rels, c =
    let n = List.length rels in
    let s,s' = List.chop n s in
    let k = sign_kind s in
    let empty_s = (k == EmptySig || k == SafeLogicalSig) in
    if lang () == Ocaml && empty_s && not (gentypvar_ok c)
      && not (List.is_empty s') && not (Int.equal (type_maxvar t) 0)
    then decomp_lams_eta_n (n+1) n env body typ
    else rels,c
  in
  let n = List.length rels in
  let s = List.firstn n s in
  let l,l' = List.chop n l in
  let t' = type_recomp (l',t') in
  (* The initial ML environment. *)
  let mle = List.fold_left Mlenv.push_std_type Mlenv.empty l in
  (* The lambdas names. *)
  let ids = List.map (fun (n,_) -> Id (id_of_name n)) rels in
  (* The according Coq environment. *)
  let env = push_rels_assum rels env in
  (* The real extraction: *)
  let e = extract_term env mle t' c [] in
  (* Expunging term and type from dummy lambdas. *)
  let trm = term_expunge s (ids,e) in
  let trm = handle_exn (ConstRef kn) n (fun i -> fst (List.nth rels (i-1))) trm
  in
  trm, type_expunge_from_sign env s t

(* Extracts the type of an axiom, honors the Extraction Implicit declaration. *)
let extract_axiom env kn typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = snd (record_constant_type env kn (Some typ)) in
  (* The real type [t']: without head products, expanded, *)
  (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
  let l,_ = type_decomp (expand env (var2var' t)) in
  let s = List.map (type2sign env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits (ConstRef kn) s 0 in
  type_expunge_from_sign env s t

let extract_fixpoint env vkn (fi,ti,ci) =
  let n = Array.length vkn in
  let types = Array.make n (Tdummy Kother)
  and terms = Array.make n MLdummy in
  let kns = Array.to_list vkn in
  current_fixpoints := kns;
  (* for replacing recursive calls [Rel ..] by the corresponding [Const]: *)
  let sub = List.rev_map mkConst kns in
  for i = 0 to n-1 do
    if sort_of env ti.(i) != InProp then begin
      let e,t = extract_std_constant env vkn.(i) (substl sub ci.(i)) ti.(i) in
      terms.(i) <- e;
      types.(i) <- t;
    end
  done;
  current_fixpoints := [];
  Dfix (Array.map (fun kn -> ConstRef kn) vkn, terms, types)

let extract_constant env kn cb =
  let r = ConstRef kn in
  let typ = Typeops.type_of_constant_type env cb.const_type in
  let warn_info () = if not (is_custom r) then add_info_axiom r in
  let warn_log () = if not (constant_has_body cb) then add_log_axiom r
  in
  let mk_typ_ax () =
    let n = type_scheme_nb_args env typ in
    let ids = iterate (fun l -> anonymous_name::l) n [] in
    Dtype (r, ids, Taxiom)
  in
  let mk_typ c =
    let s,vl = type_sign_vl env typ in
    let db = db_from_sign s in
    let t = extract_type_scheme env db c (List.length s)
    in Dtype (r, vl, t)
  in
  let mk_ax () =
    let t = extract_axiom env kn typ in
    Dterm (r, MLaxiom, t)
  in
  let mk_def c =
    let e,t = extract_std_constant env kn c typ in
    Dterm (r,e,t)
  in
  match flag_of_type env typ with
    | (Logic,TypeScheme) -> warn_log (); Dtype (r, [], Tdummy Ktype)
    | (Logic,Default) -> warn_log (); Dterm (r, MLdummy, Tdummy Kother)
    | (Info,TypeScheme) ->
        (match cb.const_body with
	  | Undef _ -> warn_info (); mk_typ_ax ()
	  | Def c -> mk_typ (Mod_subst.force_constr c)
	  | OpaqueDef c ->
	    add_opaque r;
	    if access_opaque () then
              mk_typ (Opaqueproof.force_proof (Environ.opaque_tables env) c)
            else mk_typ_ax ())
    | (Info,Default) ->
        (match cb.const_body with
	  | Undef _ -> warn_info (); mk_ax ()
	  | Def c -> mk_def (Mod_subst.force_constr c)
	  | OpaqueDef c ->
	    add_opaque r;
	    if access_opaque () then
              mk_def (Opaqueproof.force_proof (Environ.opaque_tables env) c)
            else mk_ax ())

let extract_constant_spec env kn cb =
  let r = ConstRef kn in
  let typ = Typeops.type_of_constant_type env cb.const_type in
  match flag_of_type env typ with
    | (Logic, TypeScheme) -> Stype (r, [], Some (Tdummy Ktype))
    | (Logic, Default) -> Sval (r, Tdummy Kother)
    | (Info, TypeScheme) ->
	let s,vl = type_sign_vl env typ in
	(match cb.const_body with
	  | Undef _ | OpaqueDef _ -> Stype (r, vl, None)
	  | Def body ->
	      let db = db_from_sign s in
              let body = Mod_subst.force_constr body in
	      let t = extract_type_scheme env db body (List.length s)
	      in Stype (r, vl, Some t))
    | (Info, Default) ->
	let t = snd (record_constant_type env kn (Some typ)) in
	Sval (r, type_expunge env t)

let extract_with_type env c =
  let typ = type_of env c in
  match flag_of_type env typ with
    | (Info, TypeScheme) ->
	let s,vl = type_sign_vl env typ in
	let db = db_from_sign s in
	let t = extract_type_scheme env db c (List.length s) in
	Some (vl, t)
    | _ -> None

let extract_constr env c =
  reset_meta_count ();
  let typ = type_of env c in
  match flag_of_type env typ with
    | (_,TypeScheme) -> MLdummy, Tdummy Ktype
    | (Logic,_) -> MLdummy, Tdummy Kother
    | (Info,Default) ->
      let mlt = extract_type env [] 1 typ [] in
      extract_term env Mlenv.empty mlt c [], mlt

let extract_inductive env kn =
  let ind = extract_ind env kn in
  add_recursors env kn;
  let f i j l =
    let implicits = implicits_of_global (ConstructRef ((kn,i),j+1)) in
    let rec filter i = function
      | [] -> []
      | t::l ->
	  let l' = filter (succ i) l in
	  if isDummy (expand env t) || Int.List.mem i implicits then l'
	  else t::l'
    in filter (1+ind.ind_nparams) l
  in
  let packets =
    Array.mapi (fun i p -> { p with ip_types = Array.mapi (f i) p.ip_types })
      ind.ind_packets
  in { ind with ind_packets = packets }

(*s Is a [ml_decl] logical ? *)

let logical_decl = function
  | Dterm (_,MLdummy,Tdummy _) -> true
  | Dtype (_,[],Tdummy _) -> true
  | Dfix (_,av,tv) ->
      (Array.for_all ((==) MLdummy) av) &&
      (Array.for_all isDummy tv)
  | Dind (_,i) -> Array.for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

(*s Is a [ml_spec] logical ? *)

let logical_spec = function
  | Stype (_, [], Some (Tdummy _)) -> true
  | Sval (_,Tdummy _) -> true
  | Sind (_,i) -> Array.for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false
