(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open CErrors
open Util
open Names
open Constr
open Context
open Term
open EConstr
open Vars
open Inductiveops
open Glob_term
open Glob_ops
open Termops
open Namegen
open Libnames
open Globnames
open Mod_subst
open Context.Rel.Declaration
open Ltac_pretype

type detyping_flags = {
  flg_lax : bool;
  flg_isgoal : bool;
}

(** Reimplementation of kernel case expansion functions in more lenient way *)
module RobustExpand :
sig
val return_clause : Environ.env -> Evd.evar_map -> Ind.t ->
  EInstance.t -> EConstr.t array -> EConstr.case_return -> rel_context * EConstr.t
val branch : Environ.env -> Evd.evar_map -> Construct.t ->
  EInstance.t -> EConstr.t array -> EConstr.case_branch -> rel_context * EConstr.t
end =
struct
open CVars
open Declarations
open Univ
open Constr

let instantiate_context u subst nas ctx =
  let rec instantiate i ctx = match ctx with
  | [] -> []
  | LocalAssum (_, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    LocalAssum (nas.(i), ty) :: ctx
  | LocalDef (_, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let bdy = substnl subst i (subst_instance_constr u bdy) in
    LocalDef (nas.(i), ty, bdy) :: ctx
  in
  let () = if not (Int.equal (Array.length nas) (List.length ctx)) then raise_notrace Exit in
  instantiate (Array.length nas - 1) ctx

let return_clause env sigma ind u params (nas, p) =
  try
    let u = EConstr.Unsafe.to_instance u in
    let params = EConstr.Unsafe.to_constr_array params in
    let () = if not @@ Environ.mem_mind (fst ind) env then raise_notrace Exit in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    let paramdecl = subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = subst_of_rel_context_instance paramdecl params in
    let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let self =
      let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
      let inst = Instance.of_array (Array.init (Instance.length u) Level.var) in
      mkApp (mkIndU (ind, inst), args)
    in
    let realdecls = LocalAssum (Context.anonR, self) :: realdecls in
    let realdecls = instantiate_context u paramsubst nas realdecls in
    List.map EConstr.of_rel_decl realdecls, p
  with e when CErrors.noncritical e ->
    let dummy na = LocalAssum (na, EConstr.mkProp) in
    List.rev (Array.map_to_list dummy nas), p

let branch env sigma (ind, i) u params (nas, br) =
  try
    let u = EConstr.Unsafe.to_instance u in
    let params = EConstr.Unsafe.to_constr_array params in
    let () = if not @@ Environ.mem_mind (fst ind) env then raise_notrace Exit in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    let paramdecl = subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = subst_of_rel_context_instance paramdecl params in
    let (ctx, _) = mip.mind_nf_lc.(i - 1) in
    let ctx, _ = List.chop mip.mind_consnrealdecls.(i - 1) ctx in
    let ctx = instantiate_context u paramsubst nas ctx in
    List.map EConstr.of_rel_decl ctx, br
  with e when CErrors.noncritical e ->
    let dummy na = LocalAssum (na, EConstr.mkProp) in
    List.rev (Array.map_to_list dummy nas), br

end

module Avoid :
sig
  type t
  val make : fast:bool -> Id.Set.t -> t
  val compute_name : Evd.evar_map -> let_in:bool -> pattern:bool ->
    detyping_flags -> t -> Name.t list * 'a -> Name.t ->
    EConstr.constr -> Name.t * t
  val next_name_away : detyping_flags -> Name.t -> t -> Id.t * t
end =
struct

open Nameops

type t =
| Nice of Id.Set.t
| Fast of Subscript.t Id.Map.t
  (** Overapproximation of the set of names to avoid. If [(id ↦ s) ∈ m] then for
      all subscript [s'] smaller than [s], [add_subscript id s'] needs to be
      avoided. *)

let make ~fast ids =
  if fast then
    let fold id accu =
      let id, ss = get_subscript id in
      let old_ss = try Id.Map.find id accu with Not_found -> Subscript.zero in
      if Subscript.compare ss old_ss <= 0 then accu else Id.Map.add id ss accu
    in
    let avoid = Id.Set.fold fold ids Id.Map.empty in
    Fast avoid
  else Nice ids

let fresh_id_in id avoid =
  let id, _ = get_subscript id in
  (* Find the first free subscript for that identifier *)
  let ss = try Subscript.succ (Id.Map.find id avoid) with Not_found -> Subscript.zero in
  let avoid = Id.Map.add id ss avoid in
  (add_subscript id ss, avoid)

let compute_name sigma ~let_in ~pattern flags avoid env na c =
match avoid with
| Nice avoid ->
  let flags =
    if flags.flg_isgoal then RenamingForGoal
    else if pattern then RenamingForCasesPattern (fst env, c)
    else RenamingElsewhereFor (fst env, c)
  in
  let na, avoid =
    if let_in then compute_displayed_let_name_in (Global.env ()) sigma flags avoid na
    else compute_displayed_name_in (Global.env ()) sigma flags avoid na c
  in
  na, Nice avoid
| Fast avoid ->
  (* In fast mode, we use a dumber algorithm but algorithmically more
      efficient algorithm that doesn't iterate through the term to find the
      used constants and variables. *)
  let id = match na with
  | Name id -> id
  | Anonymous ->
    if flags.flg_isgoal then default_non_dependent_ident
    else if pattern then default_dependent_ident
    else default_non_dependent_ident
  in
  let id, avoid = fresh_id_in id avoid in
  (Name id, Fast avoid)

let next_name_away flags na avoid = match avoid with
| Nice avoid ->
  let id = next_name_away na avoid in
  id, Nice (Id.Set.add id avoid)
| Fast avoid ->
  let id = match na with
  | Anonymous -> default_non_dependent_ident
  | Name id -> id
  in
  let id, avoid = fresh_id_in id avoid in
  (id, Fast avoid)

end

let compute_name = Avoid.compute_name
let next_name_away = Avoid.next_name_away

type _ delay =
| Now : 'a delay
| Later : [ `thunk ] delay

(** Should we keep details of universes during detyping ? *)
let print_universes = ref false

(** If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

let () =
  let open Goptions in
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !print_evar_arguments);
      optwrite = (:=) print_evar_arguments }

let add_name decl (nenv, env) =
  add_name (get_name decl) nenv, push_rel decl env

(****************************************************************************)
(* Tools for printing of Cases                                              *)

let encode_inductive env r =
  let indsp = Nametab.global_inductive r in
  let constr_lengths = constructors_nrealargs env indsp in
  (indsp,constr_lengths)

(* Parameterization of the translation from constr to ast      *)

(* Tables for Cases printing under a "if" form, a "let" form,  *)

let has_two_constructors lc =
  Int.equal (Array.length lc) 2 (* & lc.(0) = 0 & lc.(1) = 0 *)

let isomorphic_to_tuple lc = Int.equal (Array.length lc) 1

let encode_bool env ({CAst.loc} as r) =
  let (x,lc) = encode_inductive env r in
  if not (has_two_constructors lc) then
    user_err ?loc
      (str "This type has not exactly two constructors.");
  x

let encode_tuple env ({CAst.loc} as r) =
  let (x,lc) = encode_inductive env r in
  if not (isomorphic_to_tuple lc) then
    user_err ?loc
      (str "This type cannot be seen as a tuple type.");
  x

module PrintingInductiveMake =
  functor (Test : sig
     val encode : Environ.env -> qualid -> inductive
     val member_message : Pp.t -> bool -> Pp.t
     val field : string
     val title : string
  end) ->
  struct
    type t = inductive
    module Set = Indset
    let encode = Test.encode
    let subst subst obj = subst_ind subst obj
    let printer ind = Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef ind)
    let key = ["Printing";Test.field]
    let title = Test.title
    let member_message x = Test.member_message (printer x)
    let synchronous = true
  end

module PrintingCasesIf =
  PrintingInductiveMake (struct
    let encode = encode_bool
    let field = "If"
    let title = "Types leading to pretty-printing of Cases using a `if' form:"
    let member_message s b =
      str "Cases on elements of " ++ s ++
      str
        (if b then " are printed using a `if' form"
         else " are not printed using a `if' form")
  end)

module PrintingCasesLet =
  PrintingInductiveMake (struct
    let encode = encode_tuple
    let field = "Let"
    let title =
      "Types leading to a pretty-printing of Cases using a `let' form:"
    let member_message s b =
      str "Cases on elements of " ++ s ++
      str
        (if b then " are printed using a `let' form"
         else " are not printed using a `let' form")
  end)

module PrintingIf  = Goptions.MakeRefTable(PrintingCasesIf)
module PrintingLet = Goptions.MakeRefTable(PrintingCasesLet)

(* Flags.for printing or not wildcard and synthetisable types *)

let force_wildcard =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Wildcard"]
    ~value:true

let fast_name_generation =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Fast";"Name";"Printing"]
    ~value:false

let synthetize_type =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Synth"]
    ~value:true

let reverse_matching =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Matching"]
    ~value:true

let print_primproj_params =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Primitive";"Projection";"Parameters"]
    ~value:false

(* Auxiliary function for MutCase printing *)
(* [computable] tries to tell if the predicate typing the result is inferable*)

let computable sigma (nas, ccl) =
    (* We first remove as many lambda as the arity, then we look
       if it remains a lambda for a dependent elimination.

       Lorsque le prédicat est dépendant de manière certaine, on
       ne déclare pas le prédicat synthétisable (même si la
       variable dépendante ne l'est pas effectivement) parce que
       sinon on perd la réciprocité de la synthèse (qui, lui,
       engendrera un prédicat non dépendant) *)

  noccur_between sigma 1 (Array.length nas) ccl

let lookup_name_as_displayed env sigma t s =
  let rec lookup avoid n c = match EConstr.kind sigma c with
    | Prod (name,_,c') ->
        (match compute_displayed_name_in (Global.env ()) sigma RenamingForGoal avoid name.binder_name c' with
           | (Name id,avoid') -> if Id.equal id s then Some n else lookup avoid' (n+1) c'
           | (Anonymous,avoid') -> lookup avoid' (n+1) (pop c'))
    | LetIn (name,_,_,c') ->
        (match Namegen.compute_displayed_name_in (Global.env ()) sigma RenamingForGoal avoid name.binder_name c' with
           | (Name id,avoid') -> if Id.equal id s then Some n else lookup avoid' (n+1) c'
           | (Anonymous,avoid') -> lookup avoid' (n+1) (pop c'))
    | Cast (c,_,_) -> lookup avoid n c
    | _ -> None
  in lookup (Environ.ids_of_named_context_val (Environ.named_context_val env)) 1 t

let lookup_index_as_renamed env sigma t n =
  let rec lookup n d c = match EConstr.kind sigma c with
    | Prod (name,_,c') ->
          (match Namegen.compute_displayed_name_in (Global.env ()) sigma RenamingForGoal Id.Set.empty name.binder_name c' with
               (Name _,_) -> lookup n (d+1) c'
             | (Anonymous,_) ->
                 if Int.equal n 0 then
                   Some (d-1)
                 else if Int.equal n 1 then
                   Some d
                 else
                   lookup (n-1) (d+1) c')
    | LetIn (name,_,_,c') ->
          (match Namegen.compute_displayed_name_in (Global.env ()) sigma RenamingForGoal Id.Set.empty name.binder_name c' with
             | (Name _,_) -> lookup n (d+1) c'
             | (Anonymous,_) ->
                 if Int.equal n 0 then
                   Some (d-1)
                 else if Int.equal n 1 then
                   Some d
                 else
                   lookup (n-1) (d+1) c'
          )
    | Cast (c,_,_) -> lookup n d c
    | _ -> if Int.equal n 0 then Some (d-1) else None
  in lookup n 1 t

(**********************************************************************)
(* Factorization of match patterns *)

let print_factorize_match_patterns =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Factorizable";"Match";"Patterns"]
    ~value:true

let print_allow_match_default_opt_name =
  ["Printing";"Allow";"Match";"Default";"Clause"]
let print_allow_match_default_clause =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:print_allow_match_default_opt_name
    ~value:true

let rec join_eqns (ids,rhs as x) patll = function
  | ({CAst.loc; v=(ids',patl',rhs')} as eqn')::rest ->
     if not !Flags.raw_print && print_factorize_match_patterns () &&
        List.eq_set Id.equal ids ids' && glob_constr_eq rhs rhs'
     then
       join_eqns x (patl'::patll) rest
     else
       let eqn,rest = join_eqns x patll rest in
       eqn, eqn'::rest
  | [] ->
     patll, []

let number_of_patterns {CAst.v=(_ids,patll,_rhs)} = List.length patll

let is_default_candidate {CAst.v=(ids,_patll,_rhs)} = ids = []

let rec move_more_factorized_default_candidate_to_end eqn n = function
  | eqn' :: eqns ->
     let set,get = set_temporary_memory () in
     if is_default_candidate eqn' && set (number_of_patterns eqn') >= n then
       let isbest, dft, eqns = move_more_factorized_default_candidate_to_end eqn' (get ()) eqns in
       if isbest then false, dft, eqns else false, dft, eqn' :: eqns
     else
       let isbest, dft, eqns = move_more_factorized_default_candidate_to_end eqn n eqns in
       isbest, dft, eqn' :: eqns
  | [] -> true, Some eqn, []

let rec select_default_clause = function
  | eqn :: eqns ->
     let set,get = set_temporary_memory () in
     if is_default_candidate eqn && set (number_of_patterns eqn) > 1 then
       let isbest, dft, eqns = move_more_factorized_default_candidate_to_end eqn (get ()) eqns in
       if isbest then dft, eqns else dft, eqn :: eqns
     else
       let dft, eqns = select_default_clause eqns in dft, eqn :: eqns
  | [] -> None, []

let factorize_eqns eqns =
  let open CAst in
  let rec aux found = function
  | {loc;v=(ids,patl,rhs)}::rest ->
     let patll,rest = join_eqns (ids,rhs) [patl] rest in
     aux (CAst.make ?loc (ids,patll,rhs)::found) rest
  | [] ->
     found in
  let eqns = aux [] (List.rev eqns) in
  let mk_anon patl = List.map (fun _ -> DAst.make @@ PatVar Anonymous) patl in
  let open CAst in
  if not !Flags.raw_print && print_allow_match_default_clause () && eqns <> [] then
    match select_default_clause eqns with
    (* At least two clauses and the last one is disjunctive with no variables *)
    | Some {loc=gloc;v=([],patl::_::_,rhs)}, (_::_ as eqns) ->
      eqns@[CAst.make ?loc:gloc ([],[mk_anon patl],rhs)]
    (* Only one clause which is disjunctive with no variables: we keep at least one constructor *)
    (* so that it is not interpreted as a dummy "match" *)
    | Some {loc=gloc;v=([],patl::patl'::_,rhs)}, [] ->
      [CAst.make ?loc:gloc ([],[patl;mk_anon patl'],rhs)]
    | Some {v=((_::_,_,_ | _,([]|[_]),_))}, _ -> assert false
    | None, eqns -> eqns
  else
    eqns

(**********************************************************************)
(* Fragile algorithm to reverse pattern-matching compilation          *)

let update_name sigma na ((_,(e,_)),c) =
  match na with
  | Name _ when force_wildcard () && noccurn sigma (List.index Name.equal na e) c ->
      Anonymous
  | _ ->
      na

let decomp_branch flags e sigma (ctx, c) =
  let n = List.length ctx in
  let rec aux i nal (avoid, env as e) c =
    if Int.equal i 0 then (List.rev nal,(e,c))
    else
      let decl, c, let_in =
        match EConstr.kind sigma c with
        | Lambda (na,t,c) -> LocalAssum (na,t), c, true
        | LetIn (na,b,t,c) -> LocalDef (na,b,t), c, false
        | _ -> assert false
    in
    let na',avoid' = compute_name sigma ~let_in ~pattern:true flags avoid env (get_name decl) c in
    aux (i - 1) (na'::nal) (avoid', add_name (set_name na' decl) env) c
  in
  aux n [] e (EConstr.it_mkLambda_or_LetIn c ctx)

let rec build_tree na isgoal e sigma (ci, u, pms, cl) =
  let map i br =
    RobustExpand.branch (snd (snd e)) sigma (ci.ci_ind, i + 1) u pms br
  in
  let cl = Array.mapi map cl in
  let mkpat n rhs pl =
    let na = update_name sigma na rhs in
    na, DAst.make @@ PatCstr((ci.ci_ind,n+1),pl,na) in
  let cnl = ci.ci_pp_info.cstr_tags in
  List.flatten
    (List.init (Array.length cl)
      (fun i -> contract_branch isgoal e sigma (cnl.(i),mkpat i,cl.(i))))

and align_tree nal isgoal (e,c as rhs) sigma = match nal with
  | [] -> [Id.Set.empty,[],rhs]
  | na::nal ->
    match EConstr.kind sigma c with
    | Case (ci,u,pms,p,iv,c,cl) when
        eq_constr sigma c (mkRel (List.index Name.equal na (fst (snd e))))
        && not (Int.equal (Array.length cl) 0)
        && (* don't contract if p dependent *)
        computable sigma p (* FIXME: can do better *) ->
        let clauses = build_tree na isgoal e sigma (ci, u, pms, cl) in
        List.flatten
          (List.map (fun (ids,pat,rhs) ->
              let lines = align_tree nal isgoal rhs sigma in
              List.map (fun (ids',hd,rest) -> Id.Set.fold Id.Set.add ids ids',pat::hd,rest) lines)
            clauses)
    | _ ->
        let na = update_name sigma na rhs in
        let pat = DAst.make @@ PatVar na in
        let mat = align_tree nal isgoal rhs sigma in
        List.map (fun (ids,hd,rest) -> Nameops.Name.fold_right Id.Set.add na ids,pat::hd,rest) mat

and contract_branch isgoal e sigma (cdn,mkpat,rhs) =
  let nal,rhs = decomp_branch isgoal e sigma rhs in
  let mat = align_tree nal isgoal rhs sigma in
  List.map (fun (ids,hd,rhs) ->
      let na, pat = mkpat rhs hd in
      (Nameops.Name.fold_right Id.Set.add na ids, pat, rhs)) mat

(**********************************************************************)
(* Transform internal representation of pattern-matching into list of *)
(* clauses                                                            *)

let is_nondep_branch sigma (nas, ccl) =
  noccur_between sigma 1 (Array.length nas) ccl

let extract_nondep_branches b l =
  let rec strip l r =
    match DAst.get r, l with
      | r', [] -> r
      | GLambda (_,_,_,t), false::l -> strip l t
      | GLetIn (_,_,_,t), true::l -> strip l t
      (* FIXME: do we need adjustment? *)
      | _,_ -> assert false in
  strip l b

let it_destRLambda_or_LetIn_names l c =
  let rec aux l nal c =
    match DAst.get c, l with
      | _, [] -> (List.rev nal,c)
      | GLambda (na,_,_,c), false::l -> aux l (na::nal) c
      | GLetIn (na,_,_,c), true::l -> aux l (na::nal) c
      | _, true::l -> (* let-expansion *) aux l (Anonymous :: nal) c
      | _, false::l ->
          (* eta-expansion *)
          let next l =
            let x = next_ident_away default_dependent_ident l in
            (* Not efficient but unusual and no function to get free glob_vars *)
(* 	    if occur_glob_constr x c then next (x::l) else x in *)
            x
          in
          let x = next (free_glob_vars c) in
          let a = DAst.make @@ GVar x in
          aux l (Name x :: nal)
            (match DAst.get c with
              | GApp (p,l) -> DAst.make ?loc:c.CAst.loc @@ GApp (p,l@[a])
              | _ -> DAst.make @@ GApp (c,[a]))
  in aux l [] c

let detype_case computable detype detype_eqns avoid env sigma (ci, univs, params, p, iv, c, bl) =
  let synth_type = synthetize_type () in
  let tomatch = detype c in
  let tomatch = match iv with
    | NoInvert -> tomatch
    | CaseInvert {indices} ->
      (* XXX use holes instead of params? *)
      let t = mkApp (mkIndU (ci.ci_ind,univs), Array.append params indices) in
      DAst.make @@ GCast (tomatch, DEFAULTcast, detype t)
  in
  let alias, aliastyp, pred =
    if (not !Flags.raw_print) && synth_type && computable && not (Int.equal (Array.length bl) 0)
    then
      Anonymous, None, None
    else
      let (ctx, p) = RobustExpand.return_clause (snd env) sigma ci.ci_ind univs params p in
      let p = EConstr.it_mkLambda_or_LetIn p ctx in
      let p = detype p in
      let nl,typ = it_destRLambda_or_LetIn_names ci.ci_pp_info.ind_tags p in
      let n,typ = match DAst.get typ with
        | GLambda (x,_,t,c) -> x, c
        | _ -> Anonymous, typ in
      let aliastyp =
        if List.for_all (Name.equal Anonymous) nl then None
        else Some (CAst.make (ci.ci_ind,nl)) in
      n, aliastyp, Some typ
  in
  let constructs = Array.init (Array.length bl) (fun i -> (ci.ci_ind,i+1)) in
  let tag = let st = ci.ci_pp_info.style in
    try
      if !Flags.raw_print then
        RegularStyle
      else if st == LetPatternStyle then
        st
      else if PrintingLet.active ci.ci_ind then
        LetStyle
      else if PrintingIf.active ci.ci_ind then
        IfStyle
      else
        st
    with Not_found -> st
  in
  let constagsl = ci.ci_pp_info.cstr_tags in
  match tag, aliastyp with
  | LetStyle, None ->
      let map i br =
        let (ctx, body) = RobustExpand.branch (snd env) sigma (ci.ci_ind, i + 1) univs params br in
        EConstr.it_mkLambda_or_LetIn body ctx
      in
      let bl = Array.mapi map bl in
      let bl' = Array.map detype bl in
      let (nal,d) = it_destRLambda_or_LetIn_names constagsl.(0) bl'.(0) in
      GLetTuple (nal,(alias,pred),tomatch,d)
  | IfStyle, None ->
      if Array.for_all (fun br -> is_nondep_branch sigma br) bl then
        let map i br =
          let ctx, body = RobustExpand.branch (snd env) sigma (ci.ci_ind, i + 1) univs params br in
          EConstr.it_mkLambda_or_LetIn body ctx
        in
        let bl = Array.mapi map bl in
        let bl' = Array.map detype bl in
        let nondepbrs = Array.map2 extract_nondep_branches bl' constagsl in
        GIf (tomatch,(alias,pred), nondepbrs.(0), nondepbrs.(1))
      else
        let eqnl = detype_eqns constructs constagsl (ci, univs, params, bl) in
        GCases (tag,pred,[tomatch,(alias,aliastyp)],eqnl)
  | _ ->
      let eqnl = detype_eqns constructs constagsl (ci, univs, params, bl) in
      GCases (tag,pred,[tomatch,(alias,aliastyp)],eqnl)

let rec share_names detype flags n l avoid env sigma c t =
  match EConstr.kind sigma c, EConstr.kind sigma t with
    (* factorize even when not necessary to have better presentation *)
    | Lambda (na,t,c), Prod (na',t',c') ->
        let decl = LocalAssum (na,t) in
        let na = Nameops.Name.pick_annot na na' in
        let t' = detype flags avoid env sigma t in
        let id, avoid = next_name_away flags na.binder_name avoid in
        let env = add_name (set_name (Name id) decl) env in
        share_names detype flags (n-1) ((Name id,Explicit,None,t')::l) avoid env sigma c c'
    (* May occur for fix built interactively *)
    | LetIn (na,b,t',c), _ when n > 0 ->
        let decl = LocalDef (na,b,t') in
        let t'' = detype flags avoid env sigma t' in
        let b' = detype flags avoid env sigma b in
        let id, avoid = next_name_away flags na.binder_name avoid in
        let env = add_name (set_name (Name id) decl) env in
        share_names detype flags n ((Name id,Explicit,Some b',t'')::l) avoid env sigma c (lift 1 t)
    (* Only if built with the f/n notation or w/o let-expansion in types *)
    | _, LetIn (_,b,_,t) when n > 0 ->
        share_names detype flags n l avoid env sigma c (subst1 b t)
    (* If it is an open proof: we cheat and eta-expand *)
    | _, Prod (na',t',c') when n > 0 ->
        let decl = LocalAssum (na',t') in
        let t'' = detype flags avoid env sigma t' in
        let id, avoid = next_name_away flags na'.binder_name avoid in
        let env = add_name (set_name (Name id) decl) env in
        let appc = mkApp (lift 1 c,[|mkRel 1|]) in
        share_names detype flags (n-1) ((Name id,Explicit,None,t'')::l) avoid env sigma appc c'
    (* If built with the f/n notation: we renounce to share names *)
    | _ ->
        if n>0 then Feedback.msg_debug (strbrk "Detyping.detype: cannot factorize fix enough");
        let c = detype flags avoid env sigma c in
        let t = detype flags avoid env sigma t in
        (List.rev l,c,t)

let rec share_pattern_names detype n l avoid env sigma c t =
  let open Pattern in
  if n = 0 then
    let c = detype avoid env sigma c in
    let t = detype avoid env sigma t in
    (List.rev l,c,t)
  else match c, t with
    | PLambda (na,t,c), PProd (na',t',c') ->
        let na = match (na,na') with
            Name _, _ -> na
          | _, Name _ -> na'
          | _ -> na in
        let t' = detype avoid env sigma t in
        let id = Namegen.next_name_away na avoid in
        let avoid = Id.Set.add id avoid in
        let env = Name id :: env in
        share_pattern_names detype (n-1) ((Name id,Explicit,None,t')::l) avoid env sigma c c'
    | _ ->
        if n>0 then Feedback.msg_debug (strbrk "Detyping.detype: cannot factorize fix enough");
        let c = detype avoid env sigma c in
        let t = detype avoid env sigma t in
        (List.rev l,c,t)

let detype_fix detype flags avoid env sigma (vn,_ as nvn) (names,tys,bodies) =
  let def_avoid, def_env, lfi =
    Array.fold_left2
      (fun (avoid, env, l) na ty ->
         let id, avoid = next_name_away flags na.binder_name avoid in
         (avoid, add_name (set_name (Name id) (LocalAssum (na,ty))) env, id::l))
      (avoid, env, []) names tys in
  let n = Array.length tys in
  let v = Array.map3
    (fun c t i -> share_names detype flags (i+1) [] def_avoid def_env sigma c (lift n t))
    bodies tys vn in
  GRec(GFix (Array.map (fun i -> Some i) (fst nvn), snd nvn),Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)

let detype_cofix detype flags avoid env sigma n (names,tys,bodies) =
  let def_avoid, def_env, lfi =
    Array.fold_left2
      (fun (avoid, env, l) na ty ->
         let id, avoid = next_name_away flags na.binder_name avoid in
         (avoid, add_name (set_name (Name id) (LocalAssum (na,ty))) env, id::l))
      (avoid, env, []) names tys in
  let ntys = Array.length tys in
  let v = Array.map2
    (fun c t -> share_names detype flags 0 [] def_avoid def_env sigma c (lift ntys t))
    bodies tys in
  GRec(GCoFix n,Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)

let detype_level_name sigma l =
  if Univ.Level.is_set l then GSet else
    match UState.id_of_level (Evd.evar_universe_context sigma) l with
    | Some id -> GLocalUniv (CAst.make id)
    | None -> GUniv l

let detype_universe sigma u =
  List.map (on_fst (detype_level_name sigma)) (Univ.Universe.repr u)

let detype_sort sigma = function
  | SProp -> UNamed [GSProp,0]
  | Prop -> UNamed [GProp,0]
  | Set -> UNamed [GSet,0]
  | Type u ->
      (if !print_universes
       then UNamed (detype_universe sigma u)
       else UAnonymous {rigid=true})

type binder_kind = BProd | BLambda | BLetIn

(**********************************************************************)
(* Main detyping function                                             *)

let detype_level sigma l =
  UNamed (detype_level_name sigma l)

let detype_instance sigma l =
  if not !print_universes then None
  else
    let l = EInstance.kind sigma l in
    if Univ.Instance.is_empty l then None
    else Some (List.map (detype_level sigma) (Array.to_list (Univ.Instance.to_array l)))

let delay (type a) (d : a delay) (f : a delay -> _ -> _ -> _ -> _ -> _ -> a glob_constr_r) flags env avoid sigma t : a glob_constr_g =
  match d with
  | Now -> DAst.make (f d flags env avoid sigma t)
  | Later -> DAst.delay (fun () -> f d flags env avoid sigma t)

let rec detype d flags avoid env sigma t =
  delay d detype_r flags avoid env sigma t

and detype_r d flags avoid env sigma t =
  match EConstr.kind sigma t with
    | Rel n ->
      (try match lookup_name_of_rel n (fst env) with
         | Name id   -> GVar id
         | Anonymous ->
           let s = "_ANONYMOUS_REL_"^(string_of_int n) in
           GVar (Id.of_string s)
       with Not_found ->
         let s = "_UNBOUND_REL_"^(string_of_int n)
         in GVar (Id.of_string s))
    | Meta n ->
        (* Meta in constr are not user-parsable and are mapped to Evar *)
        if n = Constr_matching.special_meta then
          (* Using a dash to be unparsable *)
          GEvar (CAst.make @@ Id.of_string_soft "CONTEXT-HOLE", [])
        else
          GEvar (CAst.make @@ Id.of_string_soft ("M" ^ string_of_int n), [])
    | Var id ->
        (* Discriminate between section variable and non-section variable *)
        (try let _ = Global.lookup_named id in GRef (GlobRef.VarRef id, None)
         with Not_found -> GVar id)
    | Sort s -> GSort (detype_sort sigma (ESorts.kind sigma s))
    | Cast (c1,k,c2) ->
      let d1 = detype d flags avoid env sigma c1 in
      let d2 = detype d flags avoid env sigma c2 in
      GCast(d1,k,d2)
    | Prod (na,ty,c) -> detype_binder d flags BProd avoid env sigma (LocalAssum (na,ty)) c
    | Lambda (na,ty,c) -> detype_binder d flags BLambda avoid env sigma (LocalAssum (na,ty)) c
    | LetIn (na,b,ty,c) -> detype_binder d flags BLetIn avoid env sigma (LocalDef (na,b,ty)) c
    | App (f,args) ->
      let mkapp f' args' =
        match DAst.get f' with
        | GApp (f',args'') ->
          GApp (f',args''@args')
        | _ -> GApp (f',args')
      in
      mkapp (detype d flags avoid env sigma f)
        (Array.map_to_list (detype d flags avoid env sigma) args)
    | Const (sp,u) -> GRef (GlobRef.ConstRef sp, detype_instance sigma u)
    | Proj (p,c) ->
      let noparams () =
        let pars = Projection.npars p in
        let hole = DAst.make @@ GHole(Evar_kinds.InternalHole,Namegen.IntroAnonymous,None) in
        let args = List.make pars hole in
        GApp (DAst.make @@ GRef (GlobRef.ConstRef (Projection.constant p), None),
              (args @ [detype d flags avoid env sigma c]))
      in
      if flags.flg_lax || !Flags.in_debugger || !Flags.in_toplevel then
        try noparams ()
        with _ ->
            (* lax mode, used by debug printers only *)
          GApp (DAst.make @@ GRef (GlobRef.ConstRef (Projection.constant p), None),
                [detype d flags avoid env sigma c])
      else
        if print_primproj_params () then
          try
            let c = Retyping.expand_projection (snd env) sigma p c [] in
            DAst.get (detype d flags avoid env sigma c)
          with Retyping.RetypeError _ -> noparams ()
        else noparams ()

    | Evar (evk,cl) ->
        let open Context.Named.Declaration in
        let bound_to_itself_or_letin decl c =
          match decl with
          | LocalDef _ -> true
          | LocalAssum (id,_) ->
             try let n = List.index Name.equal (Name id.binder_name) (fst env) in
                 isRelN sigma n c
             with Not_found -> isVarId sigma id.binder_name c
        in
      let id,l =
        try
          let id = match Evd.evar_ident evk sigma with
          | None -> Termops.evar_suggested_name (snd env) sigma evk
          | Some id -> id
          in
          let l = Evd.evar_instance_array bound_to_itself_or_letin (Evd.find sigma evk) cl in
          (* If the instance is {x:=y; y:=y; z:=z} we print {x:=y; y:=y}
             ie the non-identity part + the variables which also instantiate other variables
             NB if the instance is {x:=f y; y:=y} we only print {x:=f y}
          *)
          let fvs,rels = List.fold_left
              (fun (fvs,rels) (_,c) -> match EConstr.kind sigma c with
                 | Rel n -> (fvs,Int.Set.add n rels)
                 | Var id -> (Id.Set.add id fvs,rels)
                 | _ -> (fvs,rels))
              (Id.Set.empty,Int.Set.empty)
              l
          in
          let l = Evd.evar_instance_array (fun d c ->
              not !print_evar_arguments
              && bound_to_itself_or_letin d c
              && not (match EConstr.kind sigma c with
                  | Rel n -> Int.Set.mem n rels
                  | Var id -> Id.Set.mem id fvs
                  | _ -> false))
              (Evd.find sigma evk)
              cl
          in
          id,List.map (fun (id,c) -> (CAst.make id,c)) l
        with Not_found ->
          Id.of_string ("X" ^ string_of_int (Evar.repr evk)),
          (List.map (fun c -> (CAst.make @@ Id.of_string "__",c)) cl)
      in
        GEvar (CAst.make id,
               List.map (on_snd (detype d flags avoid env sigma)) l)
    | Ind (ind_sp,u) ->
        GRef (GlobRef.IndRef ind_sp, detype_instance sigma u)
    | Construct (cstr_sp,u) ->
        GRef (GlobRef.ConstructRef cstr_sp, detype_instance sigma u)
    | Case (ci,u,pms,p,iv,c,bl) ->
        let comp = computable sigma p in
        let case = (ci, u, pms, p, iv, c, bl) in
        detype_case comp (detype d flags avoid env sigma)
          (detype_eqns d flags avoid env sigma comp)
          avoid env sigma case
    | Fix (nvn,recdef) -> detype_fix (detype d) flags avoid env sigma nvn recdef
    | CoFix (n,recdef) -> detype_cofix (detype d) flags avoid env sigma n recdef
    | Int i -> GInt i
    | Float f -> GFloat f
    | Array(u,t,def,ty) ->
      let t = Array.map (detype d flags avoid env sigma) t in
      let def = detype d flags avoid env sigma def in
      let ty = detype d flags avoid env sigma ty in
      let u = detype_instance sigma u in
      GArray(u, t, def, ty)

and detype_eqns d flags avoid env sigma computable constructs consnargsl bl =
  try
    if !Flags.raw_print || not (reverse_matching ()) then raise_notrace Exit;
    let mat = build_tree Anonymous flags (avoid,env) sigma bl in
    List.map (fun (ids,pat,((avoid,env),c)) ->
        CAst.make (Id.Set.elements ids,[pat],detype d flags avoid env sigma c))
      mat
  with e when CErrors.noncritical e ->
    let (ci, u, pms, bl) = bl in
    Array.to_list
      (Array.map3 (detype_eqn d flags avoid env sigma u pms) constructs consnargsl bl)

and detype_eqn d flags avoid env sigma u pms constr construct_nargs br =
  let ctx, body = RobustExpand.branch (snd env) sigma constr u pms br in
  let branch = EConstr.it_mkLambda_or_LetIn body ctx in
  let make_pat decl avoid env b ids =
    if force_wildcard () && noccurn sigma 1 b then
      DAst.make @@ PatVar Anonymous,avoid,(add_name (set_name Anonymous decl) env),ids
    else
      let na,avoid' = compute_name sigma ~let_in:false ~pattern:true flags avoid env (get_name decl) b in
      DAst.make (PatVar na),avoid',(add_name (set_name na decl) env),add_vname ids na
  in
  let rec buildrec ids patlist avoid env n b =
    if Int.equal n 0 then
      CAst.make @@
        (Id.Set.elements ids,
         [DAst.make @@ PatCstr(constr, List.rev patlist,Anonymous)],
         detype d flags avoid env sigma b)
    else match EConstr.kind sigma b with
      | Lambda (x,t,b) ->
            let pat,new_avoid,new_env,new_ids = make_pat (LocalAssum (x,t)) avoid env b ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (pred n) b

      | LetIn (x,b,t,b') ->
            let pat,new_avoid,new_env,new_ids = make_pat (LocalDef (x,b,t)) avoid env b' ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (pred n) b'

      | _ -> assert false
  in
  buildrec Id.Set.empty [] avoid env (List.length ctx) branch

and detype_binder d flags bk avoid env sigma decl c =
  let na = get_name decl in
  let body = get_value decl in
  let ty = get_type decl in
  let na',avoid' = match bk with
  | BLetIn -> compute_name sigma ~let_in:true ~pattern:false flags avoid env na c
  | _ -> compute_name sigma ~let_in:false ~pattern:false flags avoid env na c in
  let r =  detype d flags avoid' (add_name (set_name na' decl) env) sigma c in
  match bk with
  | BProd   -> GProd (na',Explicit,detype d { flags with flg_isgoal = false } avoid env sigma ty, r)
  | BLambda -> GLambda (na',Explicit,detype d { flags with flg_isgoal = false } avoid env sigma ty, r)
  | BLetIn ->
      let c = detype d { flags with flg_isgoal = false } avoid env sigma (Option.get body) in
      (* Heuristic: we display the type if in Prop *)
      let s =
        if !Flags.in_debugger then InType
        else
          (* It can fail if ty is an evar, or if run inside ocamldebug or the
             OCaml toplevel since their printers don't have access to the proper sigma/env *)
          try Retyping.get_sort_family_of (snd env) sigma ty
          with Retyping.RetypeError _ -> InType
      in
      let t = if s != InProp  && not !Flags.raw_print then None else Some (detype d { flags with flg_isgoal = false } avoid env sigma ty) in
      GLetIn (na', c, t, r)

let detype_rel_context d flags where avoid env sigma sign =
  let where = Option.map (fun c -> EConstr.it_mkLambda_or_LetIn c sign) where in
  let rec aux avoid env = function
  | [] -> []
  | decl::rest ->
      let na = get_name decl in
      let t = get_type decl in
      let na',avoid' =
        match where with
        | None -> na,avoid
        | Some c ->
          compute_name sigma ~let_in:(is_local_def decl) ~pattern:false flags avoid env na c
      in
      let b = match decl with
              | LocalAssum _ -> None
              | LocalDef (_,b,_) -> Some b
      in
      let b' = Option.map (detype d flags avoid env sigma) b in
      let t' = detype d flags avoid env sigma t in
      (na',Explicit,b',t') :: aux avoid' (add_name (set_name na' decl) env) rest
  in aux avoid env (List.rev sign)

let detype d ?(lax=false) isgoal avoid env sigma t =
  let flags = { flg_isgoal = isgoal; flg_lax = lax } in
  let avoid = Avoid.make ~fast:(fast_name_generation ()) avoid in
  detype d flags avoid (names_of_rel_context env, env) sigma t

let detype_rel_context d ?(lax = false) where avoid env sigma sign =
  let flags = { flg_isgoal = false; flg_lax = lax } in
  let avoid = Avoid.make ~fast:(fast_name_generation ()) avoid in
  detype_rel_context d flags where avoid env sigma sign

let detype_closed_glob ?lax isgoal avoid env sigma t =
  let convert_id cl id =
    try Id.Map.find id cl.idents
    with Not_found -> id
  in
  let convert_name cl = function
    | Name id -> Name (convert_id cl id)
    | Anonymous -> Anonymous
  in
  let rec detype_closed_glob cl cg : Glob_term.glob_constr = DAst.map (function
    | GVar id ->
        (* if [id] is bound to a name. *)
        begin try
          GVar(Id.Map.find id cl.idents)
        (* if [id] is bound to a typed term *)
        with Not_found -> try
          (* assumes [detype] does not raise [Not_found] exceptions *)
          let (b,c) = Id.Map.find id cl.typed in
          (* spiwack: I'm not sure it is the right thing to do,
             but I'm computing the detyping environment like
             [Printer.pr_constr_under_binders_env] does. *)
          let assums = List.map (fun id -> LocalAssum (make_annot (Name id) Sorts.Relevant,(* dummy *) mkProp)) b in
          let env = push_rel_context assums env in
          DAst.get (detype Now ?lax isgoal avoid env sigma c)
        (* if [id] is bound to a [closed_glob_constr]. *)
        with Not_found -> try
          let {closure;term} = Id.Map.find id cl.untyped in
          DAst.get (detype_closed_glob closure term)
        (* Otherwise [id] stands for itself *)
        with Not_found ->
         GVar id
        end
    | GLambda (id,k,t,c) ->
        let id = convert_name cl id in
        GLambda(id,k,detype_closed_glob cl t, detype_closed_glob cl c)
    | GProd (id,k,t,c) ->
        let id = convert_name cl id in
        GProd(id,k,detype_closed_glob cl t, detype_closed_glob cl c)
    | GLetIn (id,b,t,e) ->
        let id = convert_name cl id in
        GLetIn(id,detype_closed_glob cl b, Option.map (detype_closed_glob cl) t, detype_closed_glob cl e)
    | GLetTuple (ids,(n,r),b,e) ->
        let ids = List.map (convert_name cl) ids in
        let n = convert_name cl n in
        GLetTuple (ids,(n,r),detype_closed_glob cl b, detype_closed_glob cl e)
    | GCases (sty,po,tml,eqns) ->
        let (tml,eqns) =
          Glob_ops.map_pattern_binders (fun na -> convert_name cl na) tml eqns
        in
        let (tml,eqns) =
          Glob_ops.map_pattern (fun c -> detype_closed_glob cl c) tml eqns
        in
        GCases(sty,po,tml,eqns)
    | c ->
        DAst.get (Glob_ops.map_glob_constr (detype_closed_glob cl) cg)
    ) cg
  in
  detype_closed_glob t.closure t.term

(**********************************************************************)
(* Module substitution: relies on detyping                            *)

let rec subst_cases_pattern subst = DAst.map (function
  | PatVar _ as pat -> pat
  | PatCstr (((kn,i),j),cpl,n) as pat ->
      let kn' = subst_mind subst kn
      and cpl' = List.Smart.map (subst_cases_pattern subst) cpl in
        if kn' == kn && cpl' == cpl then pat else
          PatCstr (((kn',i),j),cpl',n)
  )

let (f_subst_genarg, subst_genarg_hook) = Hook.make ()

let rec subst_glob_constr env subst = DAst.map (function
  | GRef (ref,u) as raw ->
    let ref',t = subst_global subst ref in
    if ref' == ref then raw else (match t with
        | None -> GRef (ref', u)
        | Some t ->
          let evd = Evd.from_env env in
          let t = t.Univ.univ_abstracted_value in (* XXX This seems dangerous *)
          DAst.get (detype Now false Id.Set.empty env evd (EConstr.of_constr t)))

  | GSort _
  | GVar _
  | GEvar _
  | GInt _
  | GFloat _
  | GPatVar _ as raw -> raw

  | GApp (r,rl) as raw ->
      let r' = subst_glob_constr env subst r
      and rl' = List.Smart.map (subst_glob_constr env subst) rl in
        if r' == r && rl' == rl then raw else
          GApp(r',rl')

  | GProj ((cst,u),rl,r) as raw ->
      let rl' = List.Smart.map (subst_glob_constr env subst) rl
      and r' = subst_glob_constr env subst r in
      let ref = GlobRef.ConstRef cst in
      let ref',t = subst_global subst ref in
      assert (t = None); (* projection *)
        if ref' == ref && rl' == rl && r' == r then raw else
          GProj((destConstRef ref',u),rl',r')

  | GLambda (n,bk,r1,r2) as raw ->
      let r1' = subst_glob_constr env subst r1 and r2' = subst_glob_constr env subst r2 in
        if r1' == r1 && r2' == r2 then raw else
          GLambda (n,bk,r1',r2')

  | GProd (n,bk,r1,r2) as raw ->
      let r1' = subst_glob_constr env subst r1 and r2' = subst_glob_constr env subst r2 in
        if r1' == r1 && r2' == r2 then raw else
          GProd (n,bk,r1',r2')

  | GLetIn (n,r1,t,r2) as raw ->
      let r1' = subst_glob_constr env subst r1 in
      let r2' = subst_glob_constr env subst r2 in
      let t' = Option.Smart.map (subst_glob_constr env subst) t in
        if r1' == r1 && t == t' && r2' == r2 then raw else
          GLetIn (n,r1',t',r2')

  | GCases (sty,rtno,rl,branches) as raw ->
    let open CAst in
      let rtno' = Option.Smart.map (subst_glob_constr env subst) rtno
      and rl' = List.Smart.map (fun (a,x as y) ->
        let a' = subst_glob_constr env subst a in
        let (n,topt) = x in
        let topt' = Option.Smart.map
          (fun ({loc;v=((sp,i),y)} as t) ->
            let sp' = subst_mind subst sp in
            if sp == sp' then t else CAst.(make ?loc ((sp',i),y))) topt in
        if a == a' && topt == topt' then y else (a',(n,topt'))) rl
      and branches' = List.Smart.map
                        (fun ({loc;v=(idl,cpl,r)} as branch) ->
                           let cpl' =
                             List.Smart.map (subst_cases_pattern subst) cpl
                           and r' = subst_glob_constr env subst r in
                             if cpl' == cpl && r' == r then branch else
                               CAst.(make ?loc (idl,cpl',r')))
                        branches
      in
        if rtno' == rtno && rl' == rl && branches' == branches then raw else
          GCases (sty,rtno',rl',branches')

  | GLetTuple (nal,(na,po),b,c) as raw ->
      let po' = Option.Smart.map (subst_glob_constr env subst) po
      and b' = subst_glob_constr env subst b
      and c' = subst_glob_constr env subst c in
        if po' == po && b' == b && c' == c then raw else
          GLetTuple (nal,(na,po'),b',c')

  | GIf (c,(na,po),b1,b2) as raw ->
      let po' = Option.Smart.map (subst_glob_constr env subst) po
      and b1' = subst_glob_constr env subst b1
      and b2' = subst_glob_constr env subst b2
      and c' = subst_glob_constr env subst c in
        if c' == c && po' == po && b1' == b1 && b2' == b2 then raw else
          GIf (c',(na,po'),b1',b2')

  | GRec (fix,ida,bl,ra1,ra2) as raw ->
      let ra1' = Array.Smart.map (subst_glob_constr env subst) ra1
      and ra2' = Array.Smart.map (subst_glob_constr env subst) ra2 in
      let bl' = Array.Smart.map
        (List.Smart.map (fun (na,k,obd,ty as dcl) ->
          let ty' = subst_glob_constr env subst ty in
          let obd' = Option.Smart.map (subst_glob_constr env subst) obd in
          if ty'==ty && obd'==obd then dcl else (na,k,obd',ty')))
        bl in
        if ra1' == ra1 && ra2' == ra2 && bl'==bl then raw else
          GRec (fix,ida,bl',ra1',ra2')

  | GHole (knd, naming, solve) as raw ->
    let nknd = match knd with
    | Evar_kinds.ImplicitArg (ref, i, b) ->
      let nref, _ = subst_global subst ref in
      if nref == ref then knd else Evar_kinds.ImplicitArg (nref, i, b)
    | _ -> knd
    in
    let nsolve = Option.Smart.map (Hook.get f_subst_genarg subst) solve in
    if nsolve == solve && nknd == knd then raw
    else GHole (nknd, naming, nsolve)

  | GCast (r1,k,r2) as raw ->
      let r1' = subst_glob_constr env subst r1 in
      let r2' = subst_glob_constr env subst r2 in
      if r1' == r1 && r2' == r2 then raw else GCast (r1',k,r2')

  | GArray (u,t,def,ty) as raw ->
      let def' = subst_glob_constr env subst def
      and t' = Array.Smart.map (subst_glob_constr env subst) t
      and ty' = subst_glob_constr env subst ty
      in
        if def' == def && t' == t && ty' == ty then raw else
          GArray(u,t',def',ty')

  )
