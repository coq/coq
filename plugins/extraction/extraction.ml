(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Util
open Names
open Term
open Constr
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
open Context.Rel.Declaration
(*i*)

exception I of inductive_kind

(* A set of all fixpoint functions currently being extracted *)
let current_fixpoints = ref ([] : Constant.t list)

(* NB: In OCaml, [type_of] and [get_of] might raise
   [SingletonInductiveBecomeProp]. This exception will be caught
   in late wrappers around the exported functions of this file,
   in order to display the location of the issue. *)

let type_of env sg c =
  let polyprop = (lang() == Haskell) in
  Retyping.get_type_of ~polyprop env sg (strip_outer_cast sg c)

let sort_of env sg c =
  let polyprop = (lang() == Haskell) in
  Retyping.get_sort_family_of ~polyprop env sg (strip_outer_cast sg c)

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

let rec flag_of_type env sg t : flag =
  let t = whd_all env sg t in
  match EConstr.kind sg t with
    | Prod (x,t,c) -> flag_of_type (EConstr.push_rel (LocalAssum (x,t)) env) sg c
    | Sort s when Sorts.is_prop (EConstr.ESorts.kind sg s) -> (Logic,TypeScheme)
    | Sort _ -> (Info,TypeScheme)
    | _ -> if (sort_of env sg t) == InProp then (Logic,Default) else (Info,Default)

(*s Two particular cases of [flag_of_type]. *)

let is_default env sg t = match flag_of_type env sg t with
| (Info, Default) -> true
| _ -> false

exception NotDefault of kill_reason

let check_default env sg t =
  match flag_of_type env sg t with
    | _,TypeScheme -> raise (NotDefault Ktype)
    | Logic,_ -> raise (NotDefault Kprop)
    | _ -> ()

let is_info_scheme env sg t = match flag_of_type env sg t with
| (Info, TypeScheme) -> true
| _ -> false

let push_rel_assum (n, t) env =
  EConstr.push_rel (LocalAssum (n, t)) env

let push_rels_assum assums =
  EConstr.push_rel_context (List.map (fun (x,t) -> LocalAssum (x,t)) assums)

let get_body lconstr = EConstr.of_constr (Mod_subst.force_constr lconstr)

let get_opaque env c =
  EConstr.of_constr
    (Opaqueproof.force_proof (Environ.opaque_tables env) c)

let applistc c args = EConstr.mkApp (c, Array.of_list args)

(* Same as [Environ.push_rec_types], but for [EConstr.t] *)
let push_rec_types (lna,typarray,_) env =
  let ctxt =
    Array.map2_i
      (fun i na t -> LocalAssum (na, EConstr.Vars.lift i t)) lna typarray
  in
  Array.fold_left (fun e assum -> EConstr.push_rel assum e) env ctxt

(* Same as [Termops.nb_lam], but for [EConstr.t] *)
let nb_lam sg c = List.length (fst (EConstr.decompose_lam sg c))

(* Same as [Term.decompose_lam_n] but for [EConstr.t] *)
let decompose_lam_n sg n =
  let rec lamdec_rec l n c =
    if n <= 0 then l,c
    else match EConstr.kind sg c with
      | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | Cast (c,_,_)     -> lamdec_rec l n c
      | _ -> raise Not_found
  in
  lamdec_rec [] n

(*s [type_sign] gernerates a signature aimed at treating a type application. *)

let rec type_sign env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        (if is_info_scheme env sg t then Keep else Kill Kprop)
        :: (type_sign (push_rel_assum (n,t) env) sg d)
    | _ -> []

let rec type_scheme_nb_args env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let n = type_scheme_nb_args (push_rel_assum (n,t) env) sg d in
        if is_info_scheme env sg t then n+1 else n
    | _ -> 0

let type_scheme_nb_args' env c =
  type_scheme_nb_args env (Evd.from_env env) (EConstr.of_constr c)

let _ = Hook.set type_scheme_nb_args_hook type_scheme_nb_args'

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
  let vl = Id.Set.of_list vl in
  next_ident_away id' vl

let rec type_sign_vl env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let s,vl = type_sign_vl (push_rel_assum (n,t) env) sg d in
        if not (is_info_scheme env sg t) then Kill Kprop::s, vl
        else Keep::s, (make_typvar n vl) :: vl
    | _ -> [],[]

let rec nb_default_params env sg c =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
        let n = nb_default_params (push_rel_assum (n,t) env) sg d in
        if is_default env sg t then n+1 else n
    | _ -> 0

(* Enriching a signature with implicit information *)

let sign_with_implicits r s nb_params =
  let implicits = implicits_of_global r in
  let rec add_impl i = function
    | [] -> []
    | Keep::s when Int.Set.mem i implicits ->
       Kill (Kimplicit (r,i)) :: add_impl (i+1) s
    | sign::s -> sign :: add_impl (i+1) s
  in
  add_impl (1+nb_params) s

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
      (match Constr.kind args.(i-1) with
	 | Rel k -> Int.Map.add (relmax+1-k) j (parse (i+1) (j+1) s)
	 | _ -> parse (i+1) (j+1) s)
  in parse 1 1 si

(*S Extraction of a type. *)

(* [extract_type env db c args] is used to produce an ML type from the
   coq term [(c args)], which is supposed to be a Coq type. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

(* [j] stands for the next ML type var. [j=0] means we do not
   generate ML type var anymore (in subterms for example). *)


let rec extract_type env sg db j c args =
  match EConstr.kind sg (whd_betaiotazeta sg c) with
    | App (d, args') ->
        (* We just accumulate the arguments. *)
        extract_type env sg db j d (Array.to_list args' @ args)
    | Lambda (_,_,d) ->
	(match args with
	   | [] -> assert false (* A lambda cannot be a type. *)
           | a :: args -> extract_type env sg db j (EConstr.Vars.subst1 a d) args)
    | Prod (n,t,d) ->
	assert (List.is_empty args);
	let env' = push_rel_assum (n,t) env in
        (match flag_of_type env sg t with
	   | (Info, Default) ->
	       (* Standard case: two [extract_type] ... *)
               let mld = extract_type env' sg (0::db) j d [] in
	       (match expand env mld with
		  | Tdummy d -> Tdummy d
                  | _ -> Tarr (extract_type env sg db 0 t [], mld))
	   | (Info, TypeScheme) when j > 0 ->
	       (* A new type var. *)
               let mld = extract_type env' sg (j::db) (j+1) d [] in
	       (match expand env mld with
		  | Tdummy d -> Tdummy d
		  | _ -> Tarr (Tdummy Ktype, mld))
	   | _,lvl ->
               let mld = extract_type env' sg (0::db) j d [] in
	       (match expand env mld with
		  | Tdummy d -> Tdummy d
		  | _ ->
		      let reason = if lvl == TypeScheme then Ktype else Kprop in
		      Tarr (Tdummy reason, mld)))
    | Sort _ -> Tdummy Ktype (* The two logical cases. *)
    | _ when sort_of env sg (applistc c args) == InProp -> Tdummy Kprop
    | Rel n ->
        (match EConstr.lookup_rel n env with
           | LocalDef (_,t,_) ->
               extract_type env sg db j (EConstr.Vars.lift n t) args
	   | _ ->
	       (* Asks [db] a translation for [n]. *)
	       if n > List.length db then Tunknown
	       else let n' = List.nth db (n-1) in
	       if Int.equal n' 0 then Tunknown else Tvar n')
    | Const (kn,u) ->
        let r = ConstRef kn in
        let typ = type_of env sg (EConstr.mkConstU (kn,u)) in
        (match flag_of_type env sg typ with
	   | (Logic,_) -> assert false (* Cf. logical cases above *)
	   | (Info, TypeScheme) ->
               let mlt = extract_type_app env sg db (r, type_sign env sg typ) args in
               (match (lookup_constant kn env).const_body with
                 | Undef _ | OpaqueDef _ | Primitive _ -> mlt
                 | Def _ when is_custom (ConstRef kn) -> mlt
                 | Def lbody ->
                      let newc = applistc (get_body lbody) args in
                      let mlt' = extract_type env sg db j newc [] in
		      (* ML type abbreviations interact badly with Coq *)
		      (* reduction, so [mlt] and [mlt'] might be different: *)
		      (* The more precise is [mlt'], extracted after reduction *)
		      (* The shortest is [mlt], which use abbreviations *)
		      (* If possible, we take [mlt], otherwise [mlt']. *)
		      if eq_ml_type (expand env mlt) (expand env mlt') then mlt else mlt')
	   | (Info, Default) ->
               (* Not an ML type, for example [(c:forall X, X->X) Type nat] *)
               (match (lookup_constant kn env).const_body with
                 | Undef _  | OpaqueDef _ | Primitive _ -> Tunknown (* Brutal approx ... *)
		  | Def lbody ->
		      (* We try to reduce. *)
                      let newc = applistc (get_body lbody) args in
                      extract_type env sg db j newc []))
    | Ind ((kn,i),u) ->
        let s = (extract_ind env kn).ind_packets.(i).ip_sign in
        extract_type_app env sg db (IndRef (kn,i),s) args
    | Proj (p,t) ->
       (* Let's try to reduce, if it hasn't already been done. *)
       if Projection.unfolded p then Tunknown
       else
         extract_type env sg db j (EConstr.mkProj (Projection.unfold p, t)) args
    | Case _ | Fix _ | CoFix _ -> Tunknown
    | Evar _ | Meta _ -> Taxiom (* only possible during Show Extraction *)
    | Var v ->
       (* For Show Extraction *)
       let open Context.Named.Declaration in
       (match EConstr.lookup_named v env with
        | LocalDef (_,body,_) ->
           extract_type env sg db j (EConstr.applist (body,args)) []
        | LocalAssum (_,ty) ->
           let r = VarRef v in
           (match flag_of_type env sg ty with
            | (Logic,_) -> assert false (* Cf. logical cases above *)
            | (Info, TypeScheme) ->
              extract_type_app env sg db (r, type_sign env sg ty) args
            | (Info, Default) -> Tunknown))
    | Cast _ | LetIn _ | Construct _ | Int _ -> assert false

(*s Auxiliary function dealing with type application.
  Precondition: [r] is a type scheme represented by the signature [s],
  and is completely applied: [List.length args = List.length s]. *)

and extract_type_app env sg db (r,s) args =
  let ml_args =
    List.fold_right
      (fun (b,c) a -> if b == Keep then
         let p = List.length (fst (splay_prod env sg (type_of env sg c))) in
         let db = iterate (fun l -> 0 :: l) p db in
         (extract_type_scheme env sg db c p) :: a
       else a)
      (List.combine s args) []
  in Tglob (r, ml_args)

(*S Extraction of a type scheme. *)

(* [extract_type_scheme env db c p] works on a Coq term [c] which is
  an informative type scheme. It means that [c] is not a Coq type, but will
  be when applied to sufficiently many arguments ([p] in fact).
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

and extract_type_scheme env sg db c p =
  if Int.equal p 0 then extract_type env sg db 0 c []
  else
    let c = whd_betaiotazeta sg c in
    match EConstr.kind sg c with
      | Lambda (n,t,d) ->
          extract_type_scheme (push_rel_assum (n,t) env) sg db d (p-1)
      | _ ->
          let rels = fst (splay_prod env sg (type_of env sg c)) in
          let env = push_rels_assum rels env in
          let eta_args = List.rev_map EConstr.mkRel (List.interval 1 p) in
          extract_type env sg db 0 (EConstr.Vars.lift p c) eta_args


(*S Extraction of an inductive type. *)

(* First, a version with cache *)

and extract_ind env kn = (* kn is supposed to be in long form *)
  let mib = Environ.lookup_mind kn env in
  match lookup_ind kn mib with
  | Some ml_ind -> ml_ind
  | None ->
     try
       extract_really_ind env kn mib
     with SingletonInductiveBecomesProp id ->
       (* TODO : which inductive is concerned in the block ? *)
       error_singleton_become_prop id (Some (IndRef (kn,0)))

(* Then the real function *)

and extract_really_ind env kn mib =
    (* First, if this inductive is aliased via a Module,
       we process the original inductive if possible.
       When at toplevel of the monolithic case, we cannot do much
       (cf Vector and bug #2570) *)
    let equiv =
      if lang () != Ocaml ||
	 (not (modular ()) && at_toplevel (MutInd.modpath kn)) ||
	 KerName.equal (MutInd.canonical kn) (MutInd.user kn)
      then
	NoEquiv
      else
	begin
	  ignore (extract_ind env (MutInd.make1 (MutInd.canonical kn)));
	  Equiv (MutInd.canonical kn)
	end
    in
    (* Everything concerning parameters. *)
    (* We do that first, since they are common to all the [mib]. *)
    let mip0 = mib.mind_packets.(0) in
    let npar = mib.mind_nparams in
    let epar = push_rel_context mib.mind_params_ctxt env in
    let sg = Evd.from_env env in
    (* First pass: we store inductive signatures together with *)
    (* their type var list. *)
    let packets =
      Array.mapi
	(fun i mip ->
           let (_,u),_ = UnivGen.fresh_inductive_instance env (kn,i) in
	   let ar = Inductive.type_of_inductive env ((mib,mip),u) in
           let ar = EConstr.of_constr ar in
           let info = (fst (flag_of_type env sg ar) = Info) in
           let s,v = if info then type_sign_vl env sg ar else [],[] in
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
          let args = match Constr.kind head with
            | App (f,args) -> args (* [Constr.kind f = Ind ip] *)
            | _ -> [||]
          in
	  let dbmap = parse_ind_args p.ip_sign args (nprods + npar) in
	  let db = db_from_ind dbmap npar in
          p.ip_types.(j) <-
            extract_type_cons epar sg db dbmap (EConstr.of_constr t) (npar+1)
	done
    done;
    (* Third pass: we determine special cases. *)
    let ind_info =
      try
	let ip = (kn, 0) in
	let r = IndRef ip in
	if is_custom r then raise (I Standard);
        if mib.mind_finite == CoFinite then raise (I Coinductive);
	if not (Int.equal mib.mind_ntypes 1) then raise (I Standard);
	let p,u = packets.(0) in
	if p.ip_logical then raise (I Standard);
	if not (Int.equal (Array.length p.ip_types) 1) then raise (I Standard);
	let typ = p.ip_types.(0) in
	let l = List.filter (fun t -> not (isTdummy (expand env t))) typ in
	if not (keep_singleton ()) &&
	    Int.equal (List.length l) 1 && not (type_mem_kn kn (List.hd l))
	then raise (I Singleton);
	if List.is_empty l then raise (I Standard);
        if mib.mind_record == Declarations.NotRecord then raise (I Standard);
	(* Now we're sure it's a record. *)
	(* First, we find its field names. *)
	let rec names_prod t = match Constr.kind t with
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
	  | _::l, typ::typs when isTdummy (expand env typ) ->
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
          let ty = Inductive.type_of_inductive env ((mib,mip0),u) in
          let n = nb_default_params env sg (EConstr.of_constr ty) in
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

and extract_type_cons env sg db dbmap c i =
  match EConstr.kind sg (whd_all env sg c) with
    | Prod (n,t,d) ->
	let env' = push_rel_assum (n,t) env in
	let db' = (try Int.Map.find i dbmap with Not_found -> 0) :: db in
        let l = extract_type_cons env' sg db' dbmap d (i+1) in
        (extract_type env sg db 0 t []) :: l
    | _ -> []

(*s Recording the ML type abbreviation of a Coq type scheme constant. *)

and mlt_env env r = match r with
  | IndRef _ | ConstructRef _ | VarRef _ -> None
  | ConstRef kn ->
     let cb = Environ.lookup_constant kn env in
     match cb.const_body with
     | Undef _ | OpaqueDef _ | Primitive _ -> None
     | Def l_body ->
        match lookup_typedef kn cb with
        | Some _ as o -> o
        | None ->
           let sg = Evd.from_env env in
           let typ = EConstr.of_constr cb.const_type
           (* FIXME not sure if we should instantiate univs here *) in
           match flag_of_type env sg typ with
           | Info,TypeScheme ->
              let body = get_body l_body in
              let s = type_sign env sg typ in
              let db = db_from_sign s in
              let t = extract_type_scheme env sg db body (List.length s)
              in add_typedef kn cb t; Some t
           | _ -> None

and expand env = type_expand (mlt_env env)
and type2signature env = type_to_signature (mlt_env env)
let type2sign env = type_to_sign (mlt_env env)
let type_expunge env = type_expunge (mlt_env env)
let type_expunge_from_sign env = type_expunge_from_sign (mlt_env env)

(*s Extraction of the type of a constant. *)

let record_constant_type env sg kn opt_typ =
  let cb = lookup_constant kn env in
  match lookup_cst_type kn cb with
  | Some schema -> schema
  | None ->
     let typ = match opt_typ with
       | None -> EConstr.of_constr cb.const_type
       | Some typ -> typ
     in
     let mlt = extract_type env sg [] 1 typ [] in
     let schema = (type_maxvar mlt, mlt) in
     let () = add_cst_type kn cb schema in
     schema

(*S Extraction of a term. *)

(* Precondition: [(c args)] is not a type scheme, and is informative. *)

(* [mle] is a ML environment [Mlenv.t]. *)
(* [mlt] is the ML type we want our extraction of [(c args)] to have. *)

let rec extract_term env sg mle mlt c args =
  match EConstr.kind sg c with
    | App (f,a) ->
       extract_term env sg mle mlt f (Array.to_list a @ args)
    | Lambda (n, t, d) ->
	let id = id_of_name n in
	(match args with
	   | a :: l ->
	       (* We make as many [LetIn] as possible. *)
               let l' = List.map (EConstr.Vars.lift 1) l in
               let d' = EConstr.mkLetIn (Name id,a,t,applistc d l') in
               extract_term env sg mle mlt d' []
	   | [] ->
	       let env' = push_rel_assum (Name id, t) env in
	       let id, a =
                 try check_default env sg t; Id id, new_meta()
                 with NotDefault d -> Dummy, Tdummy d
	       in
	       let b = new_meta () in
	       (* If [mlt] cannot be unified with an arrow type, then magic! *)
	       let magic = needs_magic (mlt, Tarr (a, b)) in
               let d' = extract_term env' sg (Mlenv.push_type mle a) b d [] in
	       put_magic_if magic (MLlam (id, d')))
    | LetIn (n, c1, t1, c2) ->
	let id = id_of_name n in
        let env' = EConstr.push_rel (LocalDef (Name id, c1, t1)) env in
	(* We directly push the args inside the [LetIn].
           TODO: the opt_let_app flag is supposed to prevent that *)
        let args' = List.map (EConstr.Vars.lift 1) args in
	(try
          check_default env sg t1;
	  let a = new_meta () in
          let c1' = extract_term env sg mle a c1 [] in
	  (* The type of [c1'] is generalized and stored in [mle]. *)
	  let mle' =
	    if generalizable c1'
	    then Mlenv.push_gen mle a
	    else Mlenv.push_type mle a
	  in
          MLletin (Id id, c1', extract_term env' sg mle' mlt c2 args')
	with NotDefault d ->
	  let mle' = Mlenv.push_std_type mle (Tdummy d) in
          ast_pop (extract_term env' sg mle' mlt c2 args'))
    | Const (kn,_) ->
        extract_cst_app env sg mle mlt kn args
    | Construct (cp,_) ->
        extract_cons_app env sg mle mlt cp args
    | Proj (p, c) ->
        let term = Retyping.expand_projection env (Evd.from_env env) p c [] in
        extract_term env sg mle mlt term args
    | Rel n ->
	(* As soon as the expected [mlt] for the head is known, *)
	(* we unify it with an fresh copy of the stored type of [Rel n]. *)
	let extract_rel mlt = put_magic (mlt, Mlenv.get mle n) (MLrel n)
        in extract_app env sg mle mlt extract_rel args
    | Case ({ci_ind=ip},_,c0,br) ->
        extract_app env sg mle mlt (extract_case env sg mle (ip,c0,br)) args
    | Fix ((_,i),recd) ->
        extract_app env sg mle mlt (extract_fix env sg mle i recd) args
    | CoFix (i,recd) ->
        extract_app env sg mle mlt (extract_fix env sg mle i recd) args
    | Cast (c,_,_) -> extract_term env sg mle mlt c args
    | Evar _ | Meta _ -> MLaxiom
    | Var v ->
       (* Only during Show Extraction *)
       let open Context.Named.Declaration in
       let ty = match EConstr.lookup_named v env with
         | LocalAssum (_,ty) -> ty
         | LocalDef (_,_,ty) -> ty
       in
       let vty = extract_type env sg [] 0 ty [] in
       let extract_var mlt = put_magic (mlt,vty) (MLglob (VarRef v)) in
       extract_app env sg mle mlt extract_var args
    | Int i -> assert (args = []); MLuint i
    | Ind _ | Prod _ | Sort _ -> assert false

(*s [extract_maybe_term] is [extract_term] for usual terms, else [MLdummy] *)

and extract_maybe_term env sg mle mlt c =
  try check_default env sg (type_of env sg c);
    extract_term env sg mle mlt c []
  with NotDefault d ->
    put_magic (mlt, Tdummy d) (MLdummy d)

(*s Generic way to deal with an application. *)

(* We first type all arguments starting with unknown meta types.
   This gives us the expected type of the head. Then we use the
   [mk_head] to produce the ML head from this type. *)

and extract_app env sg mle mlt mk_head args =
  let metas = List.map new_meta args in
  let type_head = type_recomp (metas, mlt) in
  let mlargs = List.map2 (extract_maybe_term env sg mle) metas args in
  mlapp (mk_head type_head) mlargs

(*s Auxiliary function used to extract arguments of constant or constructor. *)

and make_mlargs env sg e s args typs =
  let rec f = function
    | [], [], _ -> []
    | a::la, t::lt, [] -> extract_maybe_term env sg e t a :: (f (la,lt,[]))
    | a::la, t::lt, Keep::s -> extract_maybe_term env sg e t a :: (f (la,lt,s))
    | _::la, _::lt, _::s -> f (la,lt,s)
    | _ -> assert false
  in f (args,typs,s)

(*s Extraction of a constant applied to arguments. *)

and extract_cst_app env sg mle mlt kn args =
  (* First, the [ml_schema] of the constant, in expanded version. *)
  let nb,t = record_constant_type env sg kn None in
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
  let mla = make_mlargs env sg mle s args metas in
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
      with e when CErrors.noncritical e -> mla
  in
  (* For strict languages, purely logical signatures lead to a dummy lam
     (except when [Kill Ktype] everywhere). So a [MLdummy] is left
     accordingly. *)
  let optdummy = match sign_kind s_full with
    | UnsafeLogicalSig when lang () != Haskell -> [MLdummy Kprop]
    | _ -> []
  in
  (* Different situations depending of the number of arguments: *)
  if la >= ls
  then
    (* Enough args, cleanup already done in [mla], we only add the
       additional dummy if needed. *)
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
   \item In ML, constructor arguments are uncurryfied.
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Coq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize} *)

and extract_cons_app env sg mle mlt (((kn,i) as ip,j) as cp) args =
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
    let mla = make_mlargs env sg mle s args' metas in
    if Int.equal la (ls + params_nb)
    then put_magic_if (magic2 && not magic1) (head mla)
    else (* [ params_nb <= la <= ls + params_nb ] *)
      let ls' = params_nb + ls - la in
      let s' = List.lastn ls' s in
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      put_magic_if magic2 (anonym_or_dummy_lams (head mla) s')

(*S Extraction of a case. *)

and extract_case env sg mle ((kn,i) as ip,c,br) mlt =
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
    let t = type_of env sg c in
    (* The only non-informative case: [c] is of sort [Prop] *)
    if (sort_of env sg t) == InProp then
      begin
	add_recursors env kn; (* May have passed unseen if logical ... *)
	(* Logical singleton case: *)
	(* [match c with C i j k -> t] becomes [t'] *)
	assert (Int.equal br_size 1);
	let s = iterate (fun l -> Kill Kprop :: l) ni.(0) [] in
	let mlt = iterate (fun t -> Tarr (Tdummy Kprop, t)) ni.(0) mlt in
        let e = extract_maybe_term env sg mle mlt br.(0) in
	snd (case_expunge s e)
      end
    else
      let mi = extract_ind env kn in
      let oi = mi.ind_packets.(i) in
      let metas = Array.init (List.length oi.ip_vars) new_meta in
      (* The extraction of the head. *)
      let type_head = Tglob (IndRef ip, Array.to_list metas) in
      let a = extract_term env sg mle type_head c [] in
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
        let e = extract_maybe_term env sg mle (type_recomp (l,mlt)) br.(i) in
	(* We suppress dummy arguments according to signature. *)
	let ids,e = case_expunge s e in
	(List.rev ids, Pusual r, e)
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

and extract_fix env sg mle i (fi,ti,ci as recd) mlt =
  let env = push_rec_types recd env in
  let metas = Array.map new_meta fi in
  metas.(i) <- mlt;
  let mle = Array.fold_left Mlenv.push_type mle metas in
  let ei = Array.map2 (extract_maybe_term env sg mle) metas ci in
  MLfix (i, Array.map id_of_name fi, ei)

(*S ML declarations. *)

(* [decomp_lams_eta env c t] finds the number [n] of products in the type [t],
   and decompose the term [c] in [n] lambdas, with eta-expansion if needed. *)

let decomp_lams_eta_n n m env sg c t =
  let rels = fst (splay_prod_n env sg n t) in
  let rels = List.map (fun (LocalAssum (id,c) | LocalDef (id,_,c)) -> (id,c)) rels in
  let rels',c = EConstr.decompose_lam sg c in
  let d = n - m in
  (* we'd better keep rels' as long as possible. *)
  let rels = (List.firstn d rels) @ rels' in
  let eta_args = List.rev_map EConstr.mkRel (List.interval 1 d) in
  rels, applistc (EConstr.Vars.lift d c) eta_args

(* Let's try to identify some situation where extracted code
   will allow generalisation of type variables *)

let rec gentypvar_ok sg c = match EConstr.kind sg c with
  | Lambda _ | Const _ -> true
  | App (c,v) ->
      (* if all arguments are variables, these variables will
	 disappear after extraction (see [empty_s] below) *)
      Array.for_all (EConstr.isRel sg) v && gentypvar_ok sg c
  | Cast (c,_,_) -> gentypvar_ok sg c
  | _ -> false

(*s From a constant to a ML declaration. *)

let extract_std_constant env sg kn body typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = snd (record_constant_type env sg kn (Some typ)) in
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
    and m = nb_lam sg body in
    if n <= m then decompose_lam_n sg n body
    else
      let s,s' = List.chop m s in
      if List.for_all ((==) Keep) s' &&
	(lang () == Haskell || sign_kind s != UnsafeLogicalSig)
      then decompose_lam_n sg m body
      else decomp_lams_eta_n n m env sg body typ
  in
  (* Should we do one eta-expansion to avoid non-generalizable '_a ? *)
  let rels, c =
    let n = List.length rels in
    let s,s' = List.chop n s in
    let k = sign_kind s in
    let empty_s = (k == EmptySig || k == SafeLogicalSig) in
    if lang () == Ocaml && empty_s && not (gentypvar_ok sg c)
      && not (List.is_empty s') && not (Int.equal (type_maxvar t) 0)
    then decomp_lams_eta_n (n+1) n env sg body typ
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
  let e = extract_term env sg mle t' c [] in
  (* Expunging term and type from dummy lambdas. *)
  let trm = term_expunge s (ids,e) in
  trm, type_expunge_from_sign env s t

(* Extracts the type of an axiom, honors the Extraction Implicit declaration. *)
let extract_axiom env sg kn typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = snd (record_constant_type env sg kn (Some typ)) in
  (* The real type [t']: without head products, expanded, *)
  (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
  let l,_ = type_decomp (expand env (var2var' t)) in
  let s = List.map (type2sign env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits (ConstRef kn) s 0 in
  type_expunge_from_sign env s t

let extract_fixpoint env sg vkn (fi,ti,ci) =
  let n = Array.length vkn in
  let types = Array.make n (Tdummy Kprop)
  and terms = Array.make n (MLdummy Kprop) in
  let kns = Array.to_list vkn in
  current_fixpoints := kns;
  (* for replacing recursive calls [Rel ..] by the corresponding [Const]: *)
  let sub = List.rev_map EConstr.mkConst kns in
  for i = 0 to n-1 do
    if sort_of env sg ti.(i) != InProp then
      try
        let e,t = extract_std_constant env sg vkn.(i)
                   (EConstr.Vars.substl sub ci.(i)) ti.(i) in
        terms.(i) <- e;
        types.(i) <- t;
      with SingletonInductiveBecomesProp id ->
        error_singleton_become_prop id (Some (ConstRef vkn.(i)))
  done;
  current_fixpoints := [];
  Dfix (Array.map (fun kn -> ConstRef kn) vkn, terms, types)

let extract_constant env kn cb =
  let sg = Evd.from_env env in
  let r = ConstRef kn in
  let typ = EConstr.of_constr cb.const_type in
  let warn_info () = if not (is_custom r) then add_info_axiom r in
  let warn_log () = if not (constant_has_body cb) then add_log_axiom r
  in
  let mk_typ_ax () =
    let n = type_scheme_nb_args env sg typ in
    let ids = iterate (fun l -> anonymous_name::l) n [] in
    Dtype (r, ids, Taxiom)
  in
  let mk_typ c =
    let s,vl = type_sign_vl env sg typ in
    let db = db_from_sign s in
    let t = extract_type_scheme env sg db c (List.length s)
    in Dtype (r, vl, t)
  in
  let mk_ax () =
    let t = extract_axiom env sg kn typ in
    Dterm (r, MLaxiom, t)
  in
  let mk_def c =
    let e,t = extract_std_constant env sg kn c typ in
    Dterm (r,e,t)
  in
  try
    match flag_of_type env sg typ with
    | (Logic,TypeScheme) -> warn_log (); Dtype (r, [], Tdummy Ktype)
    | (Logic,Default) -> warn_log (); Dterm (r, MLdummy Kprop, Tdummy Kprop)
    | (Info,TypeScheme) ->
        (match cb.const_body with
          | Primitive _ | Undef _ -> warn_info (); mk_typ_ax ()
	  | Def c ->
             (match Recordops.find_primitive_projection kn with
              | None -> mk_typ (get_body c)
              | Some p ->
                let p = Projection.make p false in
                let ind = Projection.inductive p in
                let bodies = Inductiveops.legacy_match_projection env ind in
                let body = bodies.(Projection.arg p) in
                mk_typ (EConstr.of_constr body))
	  | OpaqueDef c ->
	    add_opaque r;
            if access_opaque () then mk_typ (get_opaque env c)
            else mk_typ_ax ())
    | (Info,Default) ->
        (match cb.const_body with
          | Primitive _ | Undef _ -> warn_info (); mk_ax ()
	  | Def c ->
             (match Recordops.find_primitive_projection kn with
              | None -> mk_def (get_body c)
              | Some p ->
                let p = Projection.make p false in
                let ind = Projection.inductive p in
                let bodies = Inductiveops.legacy_match_projection env ind in
                let body = bodies.(Projection.arg p) in
                mk_def (EConstr.of_constr body))
	  | OpaqueDef c ->
	    add_opaque r;
            if access_opaque () then mk_def (get_opaque env c)
            else mk_ax ())
  with SingletonInductiveBecomesProp id ->
    error_singleton_become_prop id (Some (ConstRef kn))

let extract_constant_spec env kn cb =
  let sg = Evd.from_env env in
  let r = ConstRef kn in
  let typ = EConstr.of_constr cb.const_type in
  try
    match flag_of_type env sg typ with
    | (Logic, TypeScheme) -> Stype (r, [], Some (Tdummy Ktype))
    | (Logic, Default) -> Sval (r, Tdummy Kprop)
    | (Info, TypeScheme) ->
        let s,vl = type_sign_vl env sg typ in
	(match cb.const_body with
          | Undef _ | OpaqueDef _ | Primitive _ -> Stype (r, vl, None)
	  | Def body ->
	      let db = db_from_sign s in
              let body = get_body body in
              let t = extract_type_scheme env sg db body (List.length s)
              in Stype (r, vl, Some t))
    | (Info, Default) ->
        let t = snd (record_constant_type env sg kn (Some typ)) in
        Sval (r, type_expunge env t)
  with SingletonInductiveBecomesProp id ->
    error_singleton_become_prop id (Some (ConstRef kn))

let extract_with_type env sg c =
  try
    let typ = type_of env sg c in
    match flag_of_type env sg typ with
    | (Info, TypeScheme) ->
        let s,vl = type_sign_vl env sg typ in
        let db = db_from_sign s in
        let t = extract_type_scheme env sg db c (List.length s) in
        Some (vl, t)
    | _ -> None
  with SingletonInductiveBecomesProp id ->
    error_singleton_become_prop id None

let extract_constr env sg c =
  reset_meta_count ();
  try
    let typ = type_of env sg c in
    match flag_of_type env sg typ with
    | (_,TypeScheme) -> MLdummy Ktype, Tdummy Ktype
    | (Logic,_) -> MLdummy Kprop, Tdummy Kprop
    | (Info,Default) ->
       let mlt = extract_type env sg [] 1 typ [] in
       extract_term env sg Mlenv.empty mlt c [], mlt
  with SingletonInductiveBecomesProp id ->
    error_singleton_become_prop id None

let extract_inductive env kn =
  let ind = extract_ind env kn in
  add_recursors env kn;
  let f i j l =
    let implicits = implicits_of_global (ConstructRef ((kn,i),j+1)) in
    let rec filter i = function
      | [] -> []
      | t::l ->
	  let l' = filter (succ i) l in
	  if isTdummy (expand env t) || Int.Set.mem i implicits then l'
	  else t::l'
    in filter (1+ind.ind_nparams) l
  in
  let packets =
    Array.mapi (fun i p -> { p with ip_types = Array.mapi (f i) p.ip_types })
      ind.ind_packets
  in { ind with ind_packets = packets }

(*s Is a [ml_decl] logical ? *)

let logical_decl = function
  | Dterm (_,MLdummy _,Tdummy _) -> true
  | Dtype (_,[],Tdummy _) -> true
  | Dfix (_,av,tv) ->
      (Array.for_all isMLdummy av) &&
      (Array.for_all isTdummy tv)
  | Dind (_,i) -> Array.for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

(*s Is a [ml_spec] logical ? *)

let logical_spec = function
  | Stype (_, [], Some (Tdummy _)) -> true
  | Sval (_,Tdummy _) -> true
  | Sind (_,i) -> Array.for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false
