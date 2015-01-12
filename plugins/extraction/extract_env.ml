(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Miniml
open Term
open Declarations
open Names
open Libnames
open Globnames
open Pp
open Errors
open Util
open Table
open Extraction
open Modutil
open Common
open Mod_subst

(***************************************)
(*S Part I: computing Coq environment. *)
(***************************************)

let toplevel_env () =
  let get_reference = function
    | (_,kn), Lib.Leaf o ->
	let mp,_,l = repr_kn kn in
	begin match Libobject.object_tag o with
	  | "CONSTANT" ->
            let constant = Global.lookup_constant (constant_of_kn kn) in
            Some (l, SFBconst constant)
	  | "INDUCTIVE" ->
            let inductive = Global.lookup_mind (mind_of_kn kn) in
            Some (l, SFBmind inductive)
	  | "MODULE" ->
            let modl = Global.lookup_module (MPdot (mp, l)) in
            Some (l, SFBmodule modl)
	  | "MODULE TYPE" ->
            let modtype = Global.lookup_modtype (MPdot (mp, l)) in
            Some (l, SFBmodtype modtype)
          | "INCLUDE" -> error "No extraction of toplevel Include yet."
	  | _ -> None
        end
    | _ -> None
  in
  List.rev (List.map_filter get_reference (Lib.contents ()))


let environment_until dir_opt =
  let rec parse = function
    | [] when Option.is_empty dir_opt -> [Lib.current_mp (), toplevel_env ()]
    | [] -> []
    | d :: l ->
      let meb =
        Modops.destr_nofunctor (Global.lookup_module (MPfile d)).mod_type
      in
      match dir_opt with
      | Some d' when DirPath.equal d d' -> [MPfile d, meb]
      | _ -> (MPfile d, meb) :: (parse l)
  in parse (Library.loaded_libraries ())


(*s Visit:
  a structure recording the needed dependencies for the current extraction *)

module type VISIT = sig
  (* Reset the dependencies by emptying the visit lists *)
  val reset : unit -> unit

  (* Add the module_path and all its prefixes to the mp visit list.
     We'll keep all fields of these modules. *)
  val add_mp_all : module_path -> unit

  (* Add reference / ... in the visit lists.
     These functions silently add the mp of their arg in the mp list *)
  val add_ref : global_reference -> unit
  val add_decl_deps : ml_decl -> unit
  val add_spec_deps : ml_spec -> unit

  (* Test functions:
     is a particular object a needed dependency for the current extraction ? *)
  val needed_ind : mutual_inductive -> bool
  val needed_con : constant -> bool
  val needed_mp : module_path -> bool
  val needed_mp_all : module_path -> bool
end

module Visit : VISIT = struct
  type must_visit =
      { mutable ind : KNset.t; mutable con : KNset.t;
	mutable mp : MPset.t; mutable mp_all : MPset.t }
  (* the imperative internal visit lists *)
  let v = { ind = KNset.empty ; con = KNset.empty ;
	    mp = MPset.empty; mp_all = MPset.empty }
  (* the accessor functions *)
  let reset () =
    v.ind <- KNset.empty;
    v.con <- KNset.empty;
    v.mp <- MPset.empty;
    v.mp_all <- MPset.empty
  let needed_ind i = KNset.mem (user_mind i) v.ind
  let needed_con c = KNset.mem (user_con c) v.con
  let needed_mp mp = MPset.mem mp v.mp || MPset.mem mp v.mp_all
  let needed_mp_all mp = MPset.mem mp v.mp_all
  let add_mp mp =
    check_loaded_modfile mp; v.mp <- MPset.union (prefixes_mp mp) v.mp
  let add_mp_all mp =
    check_loaded_modfile mp; v.mp <- MPset.union (prefixes_mp mp) v.mp;
    v.mp_all <- MPset.add mp v.mp_all
  let add_ind i =
    let kn = user_mind i in
    v.ind <- KNset.add kn v.ind; add_mp (modpath kn)
  let add_con c =
    let kn = user_con c in
    v.con <- KNset.add kn v.con; add_mp (modpath kn)
  let add_ref = function
    | ConstRef c -> add_con c
    | IndRef (ind,_) | ConstructRef ((ind,_),_) -> add_ind ind
    | VarRef _ -> assert false
  let add_decl_deps = decl_iter_references add_ref add_ref add_ref
  let add_spec_deps = spec_iter_references add_ref add_ref add_ref
end

let add_field_label mp = function
  | (lab, SFBconst _) -> Visit.add_ref (ConstRef (Constant.make2 mp lab))
  | (lab, SFBmind _) -> Visit.add_ref (IndRef (MutInd.make2 mp lab, 0))
  | (lab, (SFBmodule _|SFBmodtype _)) -> Visit.add_mp_all (MPdot (mp,lab))

let rec add_labels mp = function
  | MoreFunctor (_,_,m) -> add_labels mp m
  | NoFunctor sign -> List.iter (add_field_label mp) sign

exception Impossible

let check_arity env cb =
  let t = Typeops.type_of_constant_type env cb.const_type in
  if Reduction.is_arity env t then raise Impossible

let check_fix env cb i =
  match cb.const_body with
    | Def lbody ->
	(match kind_of_term (Mod_subst.force_constr lbody) with
	  | Fix ((_,j),recd) when Int.equal i j -> check_arity env cb; (true,recd)
	  | CoFix (j,recd) when Int.equal i j -> check_arity env cb; (false,recd)
	  | _ -> raise Impossible)
    | Undef _ | OpaqueDef _ -> raise Impossible

let prec_declaration_equal (na1, ca1, ta1) (na2, ca2, ta2) =
  Array.equal Name.equal na1 na2 &&
  Array.equal eq_constr ca1 ca2 &&
  Array.equal eq_constr ta1 ta2

let factor_fix env l cb msb =
  let _,recd as check = check_fix env cb 0 in
  let n = Array.length (let fi,_,_ = recd in fi) in
  if Int.equal n 1 then [|l|], recd, msb
  else begin
    if List.length msb < n-1 then raise Impossible;
    let msb', msb'' = List.chop (n-1) msb in
    let labels = Array.make n l in
    List.iteri
      (fun j ->
	 function
	   | (l,SFBconst cb') ->
	       let check' = check_fix env cb' (j+1) in
	       if not ((fst check : bool) == (fst check') &&
		   prec_declaration_equal (snd check) (snd check'))
	       then raise Impossible;
	       labels.(j+1) <- l;
	   | _ -> raise Impossible) msb';
    labels, recd, msb''
  end

(** Expanding a [module_alg_expr] into a version without abbreviations
    or functor applications. This is done via a detour to entries
    (hack proposed by Elie)
*)

let expand_mexpr env mp me =
  let inl = Some (Flags.get_inline_level()) in
  let sign,_,_,_ = Mod_typing.translate_mse env (Some mp) inl me in
  sign

(** Ad-hoc update of environment, inspired by [Mod_type.check_with_aux_def].
    To check with Elie. *)

let rec mp_of_mexpr = function
  | MEident mp -> mp
  | MEwith (seb,_) -> mp_of_mexpr seb
  | _ -> assert false

let env_for_mtb_with_def env mp me idl =
  let struc = Modops.destr_nofunctor me in
  let l = Label.of_id (List.hd idl) in
  let spot = function (l',SFBconst _) -> Label.equal l l' | _ -> false in
  let before = fst (List.split_when spot struc) in
  Modops.add_structure mp before empty_delta_resolver env

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to specifications. *)

let rec extract_structure_spec env mp = function
  | [] -> []
  | (l,SFBconst cb) :: msig ->
      let kn = Constant.make2 mp l in
      let s = extract_constant_spec env kn cb in
      let specs = extract_structure_spec env mp msig in
      if logical_spec s then specs
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmind _) :: msig ->
      let mind = MutInd.make2 mp l in
      let s = Sind (mind, extract_inductive env mind) in
      let specs = extract_structure_spec env mp msig in
      if logical_spec s then specs
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmodule mb) :: msig ->
      let specs = extract_structure_spec env mp msig in
      let spec = extract_mbody_spec env mb.mod_mp mb in
      (l,Smodule spec) :: specs
  | (l,SFBmodtype mtb) :: msig ->
      let specs = extract_structure_spec env mp msig in
      let spec = extract_mbody_spec env mtb.mod_mp mtb in
      (l,Smodtype spec) :: specs

(* From [module_expression] to specifications *)

(* Invariant: the [me] given to [extract_mexpr_spec] should either come
   from a [mod_type] or [type_expr] field, or their [_alg] counterparts.
   This way, any encountered [MEident] should be a true module type.
*)

and extract_mexpr_spec env mp1 (me_struct,me_alg) = match me_alg with
  | MEident mp -> Visit.add_mp_all mp; MTident mp
  | MEwith(me',WithDef(idl,c))->
      let env' = env_for_mtb_with_def env (mp_of_mexpr me') me_struct idl in
      let mt = extract_mexpr_spec env mp1 (me_struct,me') in
      (match extract_with_type env' c with (* cb may contain some kn *)
	 | None -> mt
	 | Some (vl,typ) -> MTwith(mt,ML_With_type(idl,vl,typ)))
  | MEwith(me',WithMod(idl,mp))->
      Visit.add_mp_all mp;
      MTwith(extract_mexpr_spec env mp1 (me_struct,me'), ML_With_module(idl,mp))
  | MEapply _ -> extract_msignature_spec env mp1 me_struct

and extract_mexpression_spec env mp1 (me_struct,me_alg) = match me_alg with
  | MoreFunctor (mbid, mtb, me_alg') ->
      let me_struct' = match me_struct with
	| MoreFunctor (mbid',_,me') when MBId.equal mbid' mbid -> me'
	| _ -> assert false
      in
      let mp = MPbound mbid in
      let env' = Modops.add_module_type mp mtb env in
      MTfunsig (mbid, extract_mbody_spec env mp mtb,
		extract_mexpression_spec env' mp1 (me_struct',me_alg'))
  | NoFunctor m -> extract_mexpr_spec env mp1 (me_struct,m)

and extract_msignature_spec env mp1 = function
  | NoFunctor struc ->
      let env' = Modops.add_structure mp1 struc empty_delta_resolver env in
      MTsig (mp1, extract_structure_spec env' mp1 struc)
  | MoreFunctor (mbid, mtb, me) ->
      let mp = MPbound mbid in
      let env' = Modops.add_module_type mp mtb env in
      MTfunsig (mbid, extract_mbody_spec env mp mtb,
		extract_msignature_spec env' mp1 me)

and extract_mbody_spec env mp mb = match mb.mod_type_alg with
  | Some ty -> extract_mexpression_spec env mp (mb.mod_type,ty)
  | None -> extract_msignature_spec env mp mb.mod_type

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to implementations.

   NB: when [all=false], the evaluation order of the list is
   important: last to first ensures correct dependencies.
*)

let rec extract_structure env mp ~all = function
  | [] -> []
  | (l,SFBconst cb) :: struc ->
      (try
	 let vl,recd,struc = factor_fix env l cb struc in
	 let vc = Array.map (Constant.make2 mp) vl in
	 let ms = extract_structure env mp ~all struc in
	 let b = Array.exists Visit.needed_con vc in
	 if all || b then
	   let d = extract_fixpoint env vc recd in
	   if (not b) && (logical_decl d) then ms
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms
       with Impossible ->
	 let ms = extract_structure env mp ~all struc in
	 let c = Constant.make2 mp l in
	 let b = Visit.needed_con c in
	 if all || b then
	   let d = extract_constant env c cb in
	   if (not b) && (logical_decl d) then ms
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms)
  | (l,SFBmind mib) :: struc ->
      let ms = extract_structure env mp ~all struc in
      let mind = MutInd.make2 mp l in
      let b = Visit.needed_ind mind in
      if all || b then
	let d = Dind (mind, extract_inductive env mind) in
	if (not b) && (logical_decl d) then ms
	else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
      else ms
  | (l,SFBmodule mb) :: struc ->
      let ms = extract_structure env mp ~all struc in
      let mp = MPdot (mp,l) in
      let all' = all || Visit.needed_mp_all mp in
      if all' || Visit.needed_mp mp then
	(l,SEmodule (extract_module env mp ~all:all' mb)) :: ms
      else ms
  | (l,SFBmodtype mtb) :: struc ->
      let ms = extract_structure env mp ~all struc in
      let mp = MPdot (mp,l) in
      if all || Visit.needed_mp mp then
        (l,SEmodtype (extract_mbody_spec env mp mtb)) :: ms
      else ms

(* From [module_expr] and [module_expression] to implementations *)

and extract_mexpr env mp = function
  | MEwith _ -> assert false (* no 'with' syntax for modules *)
  | me when lang () != Ocaml ->
      (* In Haskell/Scheme, we expand everything.
         For now, we also extract everything, dead code will be removed later
         (see [Modutil.optimize_struct]. *)
      extract_msignature env mp ~all:true (expand_mexpr env mp me)
  | MEident mp ->
      if is_modfile mp && not (modular ()) then error_MPfile_as_mod mp false;
      Visit.add_mp_all mp; Miniml.MEident mp
  | MEapply (me, arg) ->
      Miniml.MEapply (extract_mexpr env mp me,
	              extract_mexpr env mp (MEident arg))

and extract_mexpression env mp = function
  | NoFunctor me -> extract_mexpr env mp me
  | MoreFunctor (mbid, mtb, me) ->
      let mp1 = MPbound mbid in
      let env' = Modops.add_module_type mp1 mtb	env in
      Miniml.MEfunctor
        (mbid,
         extract_mbody_spec env mp1 mtb,
	 extract_mexpression env' mp me)

and extract_msignature env mp ~all = function
  | NoFunctor struc ->
      let env' = Modops.add_structure mp struc empty_delta_resolver env in
      Miniml.MEstruct (mp,extract_structure env' mp ~all struc)
  | MoreFunctor (mbid, mtb, me) ->
      let mp1 = MPbound mbid in
      let env' = Modops.add_module_type mp1 mtb	env in
      Miniml.MEfunctor
        (mbid,
         extract_mbody_spec env mp1 mtb,
	 extract_msignature env' mp ~all me)

and extract_module env mp ~all mb =
  (* A module has an empty [mod_expr] when :
     - it is a module variable (for instance X inside a Module F [X:SIG])
     - it is a module assumption (Declare Module).
     Since we look at modules from outside, we shouldn't have variables.
     But a Declare Module at toplevel seems legal (cf #2525). For the
     moment we don't support this situation. *)
  let impl = match mb.mod_expr with
    | Abstract -> error_no_module_expr mp
    | Algebraic me -> extract_mexpression env mp me
    | Struct sign ->
      (* This module has a signature, otherwise it would be FullStruct.
         We extract just the elements required by this signature. *)
      let () = add_labels mp mb.mod_type in
      extract_msignature env mp ~all:false sign
    | FullStruct -> extract_msignature env mp ~all mb.mod_type
  in
  (* Slight optimization: for modules without explicit signatures
     ([FullStruct] case), we build the type out of the extracted
     implementation *)
  let typ = match mb.mod_expr with
    | FullStruct ->
      assert (Option.is_empty mb.mod_type_alg);
      mtyp_of_mexpr impl
    | _ -> extract_mbody_spec env mp mb
  in
  { ml_mod_expr = impl;
    ml_mod_type = typ }

let mono_environment refs mpl =
  Visit.reset ();
  List.iter Visit.add_ref refs;
  List.iter Visit.add_mp_all mpl;
  let env = Global.env () in
  let l = List.rev (environment_until None) in
  List.rev_map
    (fun (mp,struc) ->
      mp, extract_structure env mp ~all:(Visit.needed_mp_all mp) struc)
    l

(**************************************)
(*S Part II : Input/Output primitives *)
(**************************************)

let descr () = match lang () with
  | Ocaml -> Ocaml.ocaml_descr
  | Haskell -> Haskell.haskell_descr
  | Scheme -> Scheme.scheme_descr

(* From a filename string "foo.ml" or "foo", builds "foo.ml" and "foo.mli"
   Works similarly for the other languages. *)

let default_id = Id.of_string "Main"

let mono_filename f =
  let d = descr () in
  match f with
    | None -> None, None, default_id
    | Some f ->
	let f =
	  if Filename.check_suffix f d.file_suffix then
	    Filename.chop_suffix f d.file_suffix
	  else f
	in
	let id =
	  if lang () != Haskell then default_id
	  else
            try Id.of_string (Filename.basename f)
	    with UserError _ ->
              error "Extraction: provided filename is not a valid identifier"
	in
	Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, id

(* Builds a suitable filename from a module id *)

let module_filename mp =
  let f = file_of_modfile mp in
  let d = descr () in
  Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, Id.of_string f

(*s Extraction of one decl to stdout. *)

let print_one_decl struc mp decl =
  let d = descr () in
  reset_renaming_tables AllButExternal;
  set_phase Pre;
  ignore (d.pp_struct struc);
  set_phase Impl;
  push_visible mp [];
  let ans = d.pp_decl decl in
  pop_visible ();
  ans

(*s Extraction of a ml struct to a file. *)

(** For Recursive Extraction, writing directly on stdout
    won't work with coqide, we use a buffer instead *)

let buf = Buffer.create 1000

let formatter dry file =
  let ft =
    if dry then Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())
    else
      match file with
	| Some f -> Pp_control.with_output_to f
	| None -> Format.formatter_of_buffer buf
  in
  (* We never want to see ellipsis ... in extracted code *)
  Format.pp_set_max_boxes ft max_int;
  (* We reuse the width information given via "Set Printing Width" *)
  (match Pp_control.get_margin () with
    | None -> ()
    | Some i ->
      Format.pp_set_margin ft i;
      Format.pp_set_max_indent ft (i-10));
      (* note: max_indent should be < margin above, otherwise it's ignored *)
  ft

let get_comment () =
  let s = file_comment () in
  if String.is_empty s then None
  else
    let split_comment = Str.split (Str.regexp "[ \t\n]+") s in
    Some (prlist_with_sep spc str split_comment)

let print_structure_to_file (fn,si,mo) dry struc =
  Buffer.clear buf;
  let d = descr () in
  reset_renaming_tables AllButExternal;
  let unsafe_needs = {
    mldummy = struct_ast_search ((==) MLdummy) struc;
    tdummy = struct_type_search Mlutil.isDummy struc;
    tunknown = struct_type_search ((==) Tunknown) struc;
    magic =
      if lang () != Haskell then false
      else struct_ast_search (function MLmagic _ -> true | _ -> false) struc }
  in
  (* First, a dry run, for computing objects to rename or duplicate *)
  set_phase Pre;
  let devnull = formatter true None in
  pp_with devnull (d.pp_struct struc);
  let opened = opened_libraries () in
  (* Print the implementation *)
  let cout = if dry then None else Option.map open_out fn in
  let ft = formatter dry cout in
  let comment = get_comment () in
  begin try
    (* The real printing of the implementation *)
    set_phase Impl;
    pp_with ft (d.preamble mo comment opened unsafe_needs);
    pp_with ft (d.pp_struct struc);
    Option.iter close_out cout;
  with reraise ->
    Option.iter close_out cout; raise reraise
  end;
  if not dry then Option.iter info_file fn;
  (* Now, let's print the signature *)
  Option.iter
    (fun si ->
       let cout = open_out si in
       let ft = formatter false (Some cout) in
       begin try
	 set_phase Intf;
	 pp_with ft (d.sig_preamble mo comment opened unsafe_needs);
	 pp_with ft (d.pp_sig (signature_of_structure struc));
	 close_out cout;
       with reraise ->
	 close_out cout; raise reraise
       end;
       info_file si)
    (if dry then None else si);
  (* Print the buffer content via Coq standard formatter (ok with coqide). *)
  if not (Int.equal (Buffer.length buf) 0) then begin
    Pp.msg_info (str (Buffer.contents buf));
    Buffer.reset buf
  end


(*********************************************)
(*s Part III: the actual extraction commands *)
(*********************************************)


let reset () =
  Visit.reset (); reset_tables (); reset_renaming_tables Everything

let init modular library =
  check_inside_section (); check_inside_module ();
  set_keywords (descr ()).keywords;
  set_modular modular;
  set_library library;
  reset ();
  if modular && lang () == Scheme then error_scheme ()

let warns () =
  warning_opaques (access_opaque ());
  warning_axioms ()

(* From a list of [reference], let's retrieve whether they correspond
   to modules or [global_reference]. Warn the user if both is possible. *)

let rec locate_ref = function
  | [] -> [],[]
  | r::l ->
      let q = snd (qualid_of_reference r) in
      let mpo = try Some (Nametab.locate_module q) with Not_found -> None
      and ro =
        try Some (Smartlocate.global_with_alias r)
        with Nametab.GlobalizationError _ | UserError _ -> None
      in
      match mpo, ro with
	| None, None -> Nametab.error_global_not_found q
	| None, Some r -> let refs,mps = locate_ref l in r::refs,mps
	| Some mp, None -> let refs,mps = locate_ref l in refs,mp::mps
	| Some mp, Some r ->
	    warning_both_mod_and_cst q mp r;
	    let refs,mps = locate_ref l in refs,mp::mps

(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. Also used when
    extracting to a file with the command:
    \verb!Extraction "file"! [qualid1] ... [qualidn]. *)

let full_extr f (refs,mps) =
  init false false;
  List.iter (fun mp -> if is_modfile mp then error_MPfile_as_mod mp true) mps;
  let struc = optimize_struct (refs,mps) (mono_environment refs mps) in
  warns ();
  print_structure_to_file (mono_filename f) false struc;
  reset ()

let full_extraction f lr = full_extr f (locate_ref lr)

(*s Separate extraction is similar to recursive extraction, with the output
   decomposed in many files, one per Coq .v file *)

let separate_extraction lr =
  init true false;
  let refs,mps = locate_ref lr in
  let struc = optimize_struct (refs,mps) (mono_environment refs mps) in
  warns ();
  let print = function
    | (MPfile dir as mp, sel) as e ->
	print_structure_to_file (module_filename mp) false [e]
    | _ -> assert false
  in
  List.iter print struc;
  reset ()

(*s Simple extraction in the Coq toplevel. The vernacular command
    is \verb!Extraction! [qualid]. *)

let simple_extraction r =
  Vernacentries.dump_global (Misctypes.AN r);
  match locate_ref [r] with
  | ([], [mp]) as p -> full_extr None p
  | [r],[] ->
      init false false;
      let struc = optimize_struct ([r],[]) (mono_environment [r] []) in
      let d = get_decl_in_structure r struc in
      warns ();
      let flag =
        if is_custom r then str "(** User defined extraction *)" ++ fnl()
        else mt ()
      in
      let ans = flag ++ print_one_decl struc (modpath_of_r r) d in
      reset ();
      Pp.msg_info ans
  | _ -> assert false


(*s (Recursive) Extraction of a library. The vernacular command is
  \verb!(Recursive) Extraction Library! [M]. *)

let extraction_library is_rec m =
  init true true;
  let dir_m =
    let q = qualid_of_ident m in
    try Nametab.full_name_module q with Not_found -> error_unknown_module q
  in
  Visit.add_mp_all (MPfile dir_m);
  let env = Global.env () in
  let l = List.rev (environment_until (Some dir_m)) in
  let select l (mp,struc) =
    if Visit.needed_mp mp
    then (mp, extract_structure env mp true struc) :: l
    else l
  in
  let struc = List.fold_left select [] l in
  let struc = optimize_struct ([],[]) struc in
  warns ();
  let print = function
    | (MPfile dir as mp, sel) as e ->
	let dry = not is_rec && not (DirPath.equal dir dir_m) in
	print_structure_to_file (module_filename mp) dry [e]
    | _ -> assert false
  in
  List.iter print struc;
  reset ()

let structure_for_compute c =
  init false false;
  let env = Global.env () in
  let ast, mlt = Extraction.extract_constr env c in
  let ast = Mlutil.normalize ast in
  let refs = ref Refset.empty in
  let add_ref r = refs := Refset.add r !refs in
  let () = ast_iter_references add_ref add_ref add_ref ast in
  let refs = Refset.elements !refs in
  let struc = optimize_struct (refs,[]) (mono_environment refs []) in
  let flatstruc = List.map snd (List.flatten (List.map snd struc)) in
  flatstruc, ast, mlt
