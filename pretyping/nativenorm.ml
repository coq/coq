(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open CErrors
open Term
open Constr
open Context
open Vars
open Environ
open Reduction
open Declarations
open Names
open Inductive
open Util
open Nativecode
open Nativevalues
open Context.Rel.Declaration

(** This module implements normalization by evaluation to OCaml code *)

exception Find_at of int

(* timing *)

let get_timing_enabled =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["NativeCompute"; "Timing"]
    ~value:false

(* profiling *)

let get_profiling_enabled =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["NativeCompute"; "Profiling"]
    ~value:false

(* for supported platforms, filename for profiler results *)

let profiler_platform () =
  match [@warning "-8"] Sys.os_type with
  | "Unix" ->
     let in_ch = Unix.open_process_in "uname" in
     let uname = input_line in_ch in
     let _ = close_in in_ch in
     Format.sprintf "Unix (%s)" uname
  | "Win32" -> "Windows (Win32)"
  | "Cygwin" -> "Windows (Cygwin)"

let get_profile_filename =
  Goptions.declare_string_option_and_ref
    ~depr:false
    ~key:["NativeCompute"; "Profile"; "Filename"]
    ~value:"native_compute_profile.data"

(* find unused profile filename *)
let get_available_profile_filename () =
  let profile_filename = get_profile_filename () in
  let dir = Filename.dirname profile_filename in
  let base = Filename.basename profile_filename in
  let name = Filename.remove_extension base in
  let ext = Filename.extension base in
  try
    (* unlikely race: fn deleted, another process uses fn *)
    Filename.temp_file ~temp_dir:dir (name ^ "_") ext
  with Sys_error s ->
    let msg = "When trying to find native_compute profile output file: " ^ s in
    let _ = Feedback.msg_info (Pp.str msg) in
    assert false

let invert_tag cst tag reloc_tbl =
  try
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      if Int.equal tag tagj && (cst && Int.equal arity 0 || not(cst || Int.equal arity 0)) then
        raise (Find_at j)
      else ()
    done;raise Not_found
  with Find_at j -> (j+1)

let decompose_prod env t =
  let (name,dom,codom) = destProd (whd_all env t) in
  let name = map_annot (function
      | Anonymous -> Name (Id.of_string "x")
      | na -> na) name
  in
  (name,dom,codom)

let e_whd_all = Reductionops.clos_whd_flags CClosure.all

let app_type env sigma c =
  let t = e_whd_all env sigma c in
  decompose_appvect (EConstr.Unsafe.to_constr t)

let find_rectype_a env sigma c =
  let (t, l) = app_type env sigma c in
  match kind t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

(* Instantiate inductives and parameters in constructor type *)

let construct_of_constr_notnative const env tag (ind,u) allargs =
  let mib,mip = lookup_mind_specif env ind in
  let nparams = mib.mind_nparams in
  let params = Array.sub allargs 0 nparams in
  let i = invert_tag const tag mip.mind_reloc_tbl in
  let ctyp = Inductiveops.instantiate_constructor_params ((ind,i),u) (mib,mip) (Array.to_list params) in
  (mkApp(mkConstructU((ind,i),u), params), ctyp)

let construct_of_constr const env sigma tag typ =
  let typ = Reductionops.clos_whd_flags CClosure.all env sigma (EConstr.of_constr typ) in
  let t, l = decompose_appvect (EConstr.Unsafe.to_constr typ) in
  match Constr.kind t with
  | Ind indu ->
      construct_of_constr_notnative const env tag indu l
  | _ ->
    assert (Constr.equal t (Typeops.type_of_int env));
    (mkInt (Uint63.of_int tag), t)

let construct_of_constr_const env sigma tag typ =
  fst (construct_of_constr true env sigma tag typ)

let construct_of_constr_block = construct_of_constr false

let build_branches_type env sigma mib mip (ind,u) params p =
  let rtbl = mip.mind_reloc_tbl in
  let paramsl = Array.to_list params in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let build_one_branch i =
    let typi = Inductiveops.instantiate_constructor_params ((ind,i+1),u) (mib,mip) paramsl in
    let decl,indapp = Reductionops.splay_prod env sigma (EConstr.of_constr typi) in
    let decl = List.map (on_snd EConstr.Unsafe.to_constr) decl in
    let decl_with_letin,_ = decompose_prod_assum typi in
    let ind,cargs = find_rectype_a env sigma indapp in
    let nparams = Array.length params in
    let carity = snd (rtbl.(i)) in
    let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
    let codom =
      let ndecl = List.length decl in
      let papp = mkApp(lift ndecl p,crealargs) in
      let cstr = ith_constructor_of_inductive (fst ind) (i+1) in
      let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
      let params = Array.map (lift ndecl) params in
      let dep_cstr = mkApp(mkApp(mkConstructU (cstr,snd ind),params),relargs) in
      mkApp(papp,[|dep_cstr|])
    in
    decl, decl_with_letin, codom
  in Array.init (Array.length mip.mind_nf_lc) build_one_branch

let build_case_type p realargs c =
  mkApp(mkApp(p, realargs), [|c|])

(* normalisation of values *)

let branch_of_switch lvl ans bs =
  let tbl = ans.asw_reloc in
  let branch i =
    let tag,arity = tbl.(i) in
    let ci =
      if Int.equal arity 0 then mk_const tag
      else mk_block tag (mk_rels_accu lvl arity) in
    bs ci in
  Array.init (Array.length tbl) branch

let get_proj env (ind, proj_arg) =
  let p = Environ.get_projection env ind ~proj_arg in
  Projection.make p true

let rec nf_val env sigma v typ =
  match kind_of_value v with
  | Vaccu accu -> nf_accu env sigma accu
  | Vfun f ->
      let lvl = nb_rel env in
      let name,dom,codom =
        try decompose_prod env typ
        with DestKO ->
          CErrors.anomaly
            (Pp.strbrk "Returned a functional value in a type not recognized as a product type.")
      in
      let env = push_rel (LocalAssum (name,dom)) env in
      let body = nf_val env sigma (f (mk_rel_accu lvl)) codom in
      mkLambda(name,dom,body)
  | Vconst n -> construct_of_constr_const env sigma n typ
  | Vint64 i -> i |> Uint63.of_int64 |> mkInt
  | Vfloat64 f -> f |> Float64.of_float |> mkFloat
  | Varray t -> nf_array env sigma t typ
  | Vblock b ->
      let capp,ctyp = construct_of_constr_block env sigma (block_tag b) typ in
      let args = nf_bargs env sigma b ctyp in
      mkApp(capp,args)

and nf_type env sigma v =
  match kind_of_value v with
  | Vaccu accu -> nf_accu env sigma accu
  | _ -> assert false

and nf_type_sort env sigma v =
  match kind_of_value v with
  | Vaccu accu ->
      let t,s = nf_accu_type env sigma accu in
      let s =
        try
          destSort (whd_all env s)
        with DestKO ->
          CErrors.anomaly (Pp.str "Value should be a sort")
      in
      t, s
  | _ -> assert false

and nf_accu env sigma accu =
  let atom = atom_of_accu accu in
  if Int.equal (accu_nargs accu) 0 then nf_atom env sigma atom
  else
    let a,typ = nf_atom_type env sigma atom in
    let _, args = nf_args env sigma (args_of_accu accu) typ in
    mkApp(a,Array.of_list args)

and nf_accu_type env sigma accu =
  let atom = atom_of_accu accu in
  if Int.equal (accu_nargs accu) 0 then nf_atom_type env sigma atom
  else
    let a,typ = nf_atom_type env sigma atom in
    let t, args = nf_args env sigma (args_of_accu accu) typ in
    mkApp(a,Array.of_list args), t

and nf_args env sigma args t =
  let aux arg (t,l) =
    let _,dom,codom =
      try decompose_prod env t with
        DestKO ->
        CErrors.anomaly
          (Pp.strbrk "Returned a functional value in a type not recognized as a product type.")
    in
    let c = nf_val env sigma arg dom in
    (subst1 c codom, c::l)
  in
  let t,l = Array.fold_right aux args (t,[]) in
  t, List.rev l

and nf_bargs env sigma b t =
  let t = ref t in
  let len = block_size b in
  Array.init len
    (fun i ->
      let _,dom,codom =
        try decompose_prod env !t with
          DestKO ->
          CErrors.anomaly
            (Pp.strbrk "Returned a functional value in a type not recognized as a product type.")
      in
      let c = nf_val env sigma (block_field b i) dom in
      t := subst1 c codom; c)

and nf_atom env sigma atom =
  match atom with
  | Arel i -> mkRel (nb_rel env - i)
  | Aconstant cst -> mkConstU cst
  | Aind ind -> mkIndU ind
  | Asort s -> mkSort s
  | Avar id -> mkVar id
  | Aprod(n,dom,codom) ->
    let dom, sdom = nf_type_sort env sigma dom in
    let rdom = Sorts.relevance_of_sort sdom in
    let n = make_annot n rdom in
    let vn = mk_rel_accu (nb_rel env) in
    let env = push_rel (LocalAssum (n,dom)) env in
    let codom = nf_type env sigma (codom vn) in
    mkProd(n,dom,codom)
  | Ameta (mv,_) -> mkMeta mv
  | Aproj (p, c) ->
      let c = nf_accu env sigma c in
      let p = get_proj env p in
      mkProj(p, c)
  | _ -> fst (nf_atom_type env sigma atom)

and nf_atom_type env sigma atom =
  match atom with
  | Arel i ->
      let n = (nb_rel env - i) in
      mkRel n, Typeops.type_of_relative env n
  | Aconstant cst ->
      mkConstU cst, Typeops.type_of_constant_in env cst
  | Aind ind ->
      mkIndU ind, Inductiveops.type_of_inductive env ind
  | Asort s ->
      mkSort s, Typeops.type_of_sort s
  | Avar id ->
      mkVar id, Typeops.type_of_variable env id
  | Acase(ans,accu,p,bs) ->
      let a,ta = nf_accu_type env sigma accu in
      let ((mind,_),u as ind),allargs = find_rectype_a env sigma (EConstr.of_constr ta) in
      let (mib,mip) = Inductive.lookup_mind_specif env (fst ind) in
      let nparams = mib.mind_nparams in
      let params,realargs = Array.chop nparams allargs in
      let iv = if Typeops.should_invert_case env ans.asw_ci then
          CaseInvert {indices=realargs}
        else NoInvert
      in
      let nparamdecls = Context.Rel.length (Inductive.inductive_paramdecls (mib,u)) in
      let pT =
        hnf_prod_applist_assum env nparamdecls
          (Inductiveops.type_of_inductive env ind) (Array.to_list params) in
      let p = nf_predicate env sigma ind mip params p pT in
      (* Calcul du type des branches *)
      let btypes = build_branches_type env sigma mib mip ind params p in
      (* calcul des branches *)
      let bsw = branch_of_switch (nb_rel env) ans bs in
      let mkbranch i v =
       let decl,decl_with_letin,codom = btypes.(i) in
       let b = nf_val (Termops.push_rels_assum decl env) sigma v codom in
        Termops.it_mkLambda_or_LetIn_from_no_LetIn b decl_with_letin
      in
      let branchs = Array.mapi mkbranch bsw in
      let tcase = build_case_type p realargs a in
      let ci = ans.asw_ci in
      mkCase (Inductive.contract_case env (ci, p, iv, a, branchs)), tcase
  | Afix(tt,ft,rp,s) ->
      let tt = Array.map (fun t -> nf_type_sort env sigma t) tt in
      let tt = Array.map fst tt and rt = Array.map snd tt in
      let name = Name (Id.of_string "Ffix") in
      let names = Array.map (fun s -> make_annot name (Sorts.relevance_of_sort s)) rt in
      let lvl = nb_rel env in
      let nbfix = Array.length ft in
      let fargs = mk_rels_accu lvl (Array.length ft) in
      (* Body argument of the tuple is ignored by push_rec_types *)
      let env = push_rec_types (names,tt,[||]) env in
      (* We lift here because the types of arguments (in tt) will be evaluated
         in an environment where the fixpoints have been pushed *)
      let norm_body i v = nf_val env sigma (napply v fargs) (lift nbfix tt.(i)) in
      let ft = Array.mapi norm_body ft in
      mkFix((rp,s),(names,tt,ft)), tt.(s)
  | Acofix(tt,ft,s,_) | Acofixe(tt,ft,s,_) ->
      let tt = Array.map (fun t -> nf_type_sort env sigma t) tt in
      let tt = Array.map fst tt and rt = Array.map snd tt in
      let name = Name (Id.of_string "Fcofix") in
      let lvl = nb_rel env in
      let names = Array.map (fun s -> make_annot name (Sorts.relevance_of_sort s)) rt in
      let fargs = mk_rels_accu lvl (Array.length ft) in
      let env = push_rec_types (names,tt,[||]) env in
      let ft = Array.mapi (fun i v -> nf_val env sigma (napply v fargs) tt.(i)) ft in
      mkCoFix(s,(names,tt,ft)), tt.(s)
  | Aprod(n,dom,codom) ->
      let dom,s1 = nf_type_sort env sigma dom in
      let r1 = Sorts.relevance_of_sort s1 in
      let n = make_annot n r1 in
      let vn = mk_rel_accu (nb_rel env) in
      let env = push_rel (LocalAssum (n,dom)) env in
      let codom,s2 = nf_type_sort env sigma (codom vn) in
      mkProd(n,dom,codom), Typeops.type_of_product env n s1 s2
  | Aevar(evk,args) ->
    nf_evar env sigma evk args
  | Ameta(mv,ty) ->
     let ty = nf_type env sigma ty in
     mkMeta mv, ty
  | Aproj(p,c) ->
      let c,tc = nf_accu_type env sigma c in
      let cj = make_judge c tc in
      let p = get_proj env p in
      let uj = Typeops.judge_of_projection env p cj in
      uj.uj_val, uj.uj_type


and  nf_predicate env sigma ind mip params v pT =
  match kind (whd_allnolet env pT) with
  | LetIn (name,b,t,pT) ->
      let body =
        nf_predicate (push_rel (LocalDef (name,b,t)) env) sigma ind mip params v pT in
      mkLetIn (name,b,t,body)
  | Prod (name,dom,codom) -> begin
    match kind_of_value v with
    | Vfun f ->
      let k = nb_rel env in
      let vb = f (mk_rel_accu k) in
      let body =
        nf_predicate (push_rel (LocalAssum (name,dom)) env) sigma ind mip params vb codom in
      mkLambda(name,dom,body)
    | _ -> nf_type env sigma v
    end
  | _ ->
    match kind_of_value v with
    | Vfun f ->
      let k = nb_rel env in
      let vb = f (mk_rel_accu k) in
      let name = Name (Id.of_string "c") in
      let n = mip.mind_nrealargs in
      let rargs = Array.init n (fun i -> mkRel (n-i)) in
      let params = if Int.equal n 0 then params else Array.map (lift n) params in
      let dom = mkApp(mkIndU ind,Array.append params rargs) in
      let r = Inductive.relevance_of_inductive env (fst ind) in
      let name = make_annot name r in
      let body = nf_type (push_rel (LocalAssum (name,dom)) env) sigma vb in
      mkLambda(name,dom,body)
    | _ -> nf_type env sigma v

and nf_evar env sigma evk args =
  let evi = try Evd.find sigma evk with Not_found -> assert false in
  let hyps = Environ.named_context_of_val (Evd.evar_filtered_hyps evi) in
  let ty = EConstr.to_constr ~abort_on_undefined_evars:false sigma @@ Evd.evar_concl evi in
  if List.is_empty hyps then begin
    assert (Array.is_empty args);
    mkEvar (evk, []), ty
  end
  else
    (* Let-bound arguments are present in the evar arguments but not
       in the type, so we turn the let into a product. *)
    let hyps = Context.Named.drop_bodies hyps in
    let fold accu d = Term.mkNamedProd_or_LetIn d accu in
    let t = List.fold_left fold ty hyps in
    let ty, args = nf_args env sigma args t in
    (* nf_args takes arguments in the reverse order but produces them
       in the correct one, so we have to reverse them again for the
       evar node *)
    mkEvar (evk, List.rev args), ty

and nf_array env sigma t typ =
  let ty, allargs = app_type env sigma (EConstr.of_constr typ) in
  let typ_elem = allargs.(0) in
  let vdef = Parray.default t in
  (* Do not cast into an array out of fear that floats may sneak in *)
  let init i = nf_val env sigma (Parray.get t (Uint63.of_int i)) typ_elem in
  let t = Array.init (Parray.length_int t) init in
  let u = snd (destConst ty) in
  mkArray(u, t, nf_val env sigma vdef typ_elem, typ_elem)

let evars_of_evar_map sigma =
  { Nativelambda.evars_val = Evd.existential_opt_value0 sigma;
    Nativelambda.evars_metas = Evd.meta_type0 sigma }

(* fork perf process, return profiler's process id *)
let start_profiler_linux profile_fn =
  let coq_pid = Unix.getpid () in (* pass pid of running coqtop *)
  (* we don't want to see perf's console output *)
  let dev_null = Unix.descr_of_out_channel (open_out_bin "/dev/null") in
  let _ = Feedback.msg_info (Pp.str ("Profiling to file " ^ profile_fn)) in
  let perf = "perf" in
  let profiler_pid =
    Unix.create_process
      perf
      [|perf; "record"; "-g"; "-o"; profile_fn; "-p"; string_of_int coq_pid |]
      Unix.stdin dev_null dev_null
  in
  (* doesn't seem to be a way to test whether process creation succeeded
     (create_process doesn't raise until OCaml 4.12.0) *)
  debug_native_compiler (fun () ->
    Pp.str (Format.sprintf "Native compute profiler started, pid = %d, output to: %s" profiler_pid profile_fn));
  Some profiler_pid

let start_profiler_linux fn =
  try start_profiler_linux fn
  with Unix.Unix_error _ as e ->
    Feedback.msg_info
      Pp.(str "Could not start native code profiler: " ++ str (Printexc.to_string e));
    None

(* kill profiler via SIGINT *)
let stop_profiler_linux m_pid =
  match m_pid with
  | Some pid -> (
    let _ = debug_native_compiler (fun () -> Pp.str "Stopping native code profiler") in
    try
      Unix.kill pid Sys.sigint;
      let _ = Unix.waitpid [] pid in ()
    with Unix.Unix_error (Unix.ESRCH,"kill","") ->
      Feedback.msg_info (Pp.str "Could not stop native code profiler, no such process")
  )
  | None -> ()

let start_profiler () =
  let profile_fn = get_available_profile_filename () in
  match profiler_platform () with
    "Unix (Linux)" -> start_profiler_linux profile_fn
  | _ ->
     let _ = Feedback.msg_info
       (Pp.str (Format.sprintf "Native_compute profiling not supported on the platform: %s"
                  (profiler_platform ()))) in
     None

let stop_profiler m_pid =
  match profiler_platform() with
    "Unix (Linux)" -> stop_profiler_linux m_pid
  | _ -> ()

let native_norm env sigma c ty =
  Nativelib.link_libraries ();
  let c = EConstr.Unsafe.to_constr c in
  let ty = EConstr.Unsafe.to_constr ty in
    let profile = get_profiling_enabled () in
    let print_timing = get_timing_enabled () in
    let ml_filename, prefix = Nativelib.get_ml_filename () in
    let tnc0 = Unix.gettimeofday () in
    let code, upd = mk_norm_code env (evars_of_evar_map sigma) prefix c in
    let tnc1 = Unix.gettimeofday () in
    let time_info = Format.sprintf "native_compute: Conversion to native code done in %.5f" (tnc1 -. tnc0) in
    if print_timing then Feedback.msg_info (Pp.str time_info);
    let tc0 = Unix.gettimeofday () in
    let fn = Nativelib.compile ml_filename code ~profile:profile in
    let tc1 = Unix.gettimeofday () in
    let time_info = Format.sprintf "native_compute: Compilation done in %.5f" (tc1 -. tc0) in
    if print_timing then Feedback.msg_info (Pp.str time_info);
    let profiler_pid = if profile then start_profiler () else None in
    let t0 = Unix.gettimeofday () in
    let (rt1, _) = Nativelib.execute_library ~prefix fn upd in
    let t1 = Unix.gettimeofday () in
    if profile then stop_profiler profiler_pid;
    let time_info = Format.sprintf "native_compute: Evaluation done in %.5f" (t1 -. t0) in
    if print_timing then Feedback.msg_info (Pp.str time_info);
    let res = nf_val env sigma rt1 ty in
    let t2 = Unix.gettimeofday () in
    let time_info = Format.sprintf "native_compute: Reification done in %.5f" (t2 -. t1) in
    if print_timing then Feedback.msg_info (Pp.str time_info);
    EConstr.of_constr res

let native_norm env sigma c ty =
  if not (Flags.get_native_compiler ()) then
    user_err Pp.(str "Native_compute reduction has been disabled.");
  native_norm env sigma c ty
