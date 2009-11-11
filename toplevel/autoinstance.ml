(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

(*i*)
open Pp
open Printer
open Names
open Term
open Evd
open Sign
open Libnames
(*i*)

(*s
 * Automatic detection of (some) record instances
 *)

(* Datatype for wannabe-instances: a signature is a typeclass along
   with the collection of evars corresponding to the parameters/fields
   of the class. Each evar can be uninstantiated (we're still looking
   for them) or defined (the instance for the field is fixed) *)
type signature = global_reference * evar list * evar_map

type instance_decl_function = global_reference -> rel_context -> constr list -> unit

(*
 * Search algorithm
 *)

let rec subst_evar evar def n c =
  match kind_of_term c with
    | Evar (e,_) when e=evar -> lift n def
    | _ -> map_constr_with_binders (fun n->n+1) (subst_evar evar def) n c

let subst_evar_in_evm evar def evm =
  Evd.fold
    (fun ev evi acc ->
       let evar_body = match evi.evar_body with
	 | Evd.Evar_empty -> Evd.Evar_empty
	 | Evd.Evar_defined c -> Evd.Evar_defined (subst_evar evar def 0 c) in
       let evar_concl = subst_evar evar def 0 evi.evar_concl in
       Evd.add acc ev {evi with evar_body=evar_body; evar_concl=evar_concl}
    ) evm empty

(* Tries to define ev by c in evd. Fails if ev := c1 and c1 /= c ev :
 * T1, c : T2 and T1 /= T2. Defines recursively all evars instantiated
 * by this definition. *)

let rec safe_define evm ev c =
  if not (closedn (-1) c) then raise Termops.CannotFilter else
(*  msgnl(str"safe_define "++pr_evar_map evm++spc()++str" |- ?"++Util.pr_int ev++str" := "++pr_constr c);*)
  let evi = (Evd.find evm ev) in
  let define_subst evm sigma =
    Util.Intmap.fold
      ( fun ev (e,c) evm ->
	  match kind_of_term c with Evar (i,_) when i=ev -> evm | _ ->
	    safe_define evm ev (lift (-List.length e) c)
      ) sigma evm in
  match evi.evar_body with
    | Evd.Evar_defined def ->
	define_subst evm (Termops.filtering [] Reduction.CUMUL def c)
    | Evd.Evar_empty ->
	let t = Libtypes.reduce (Typing.type_of (Global.env()) evm c) in
	let u = Libtypes.reduce (evar_concl evi) in
	let evm = subst_evar_in_evm ev c evm in
	define_subst (Evd.define ev c evm) (Termops.filtering [] Reduction.CUMUL t u)

let add_gen_ctx (cl,gen,evm) ctx : signature * constr list =
  let rec really_new_evar () =
    let ev = Evarutil.new_untyped_evar() in
    if Evd.is_evar evm ev then really_new_evar() else ev in
  let add_gen_evar (cl,gen,evm) ev ty : signature =
    let evm = Evd.add evm ev (Evd.make_evar Environ.empty_named_context_val ty) in
    (cl,ev::gen,evm) in
  let rec mksubst b = function
    | [] -> []
    | a::tl -> b::(mksubst (a::b) tl) in
  let evl = List.map (fun _ -> really_new_evar()) ctx in
  let evcl = List.map (fun i -> mkEvar (i,[||])) evl in
  let substl = List.rev (mksubst [] (evcl)) in
  let ctx = List.map2 (fun s t -> substnl s 0 t) substl ctx in
  let sign = List.fold_left2 add_gen_evar (cl,gen,evm) (List.rev evl) ctx in
  sign,evcl

(* TODO : for full proof-irrelevance in the search, provide a real
   compare function for constr instead of Pervasive's one! *)
module SubstSet : Set.S with type elt = Termops.subst
  = Set.Make (struct type t = Termops.subst
		     let compare = Util.Intmap.compare (Pervasives.compare)
	      end)

(* searches instatiations in the library for just one evar [ev] of a
   signature. [k] is called on each resulting signature *)
let complete_evar (cl,gen,evm:signature) (ev,evi) (k:signature -> unit) =
  let ev_typ = Libtypes.reduce (evar_concl evi) in
  let sort_is_prop = is_Prop (Typing.type_of (Global.env()) evm (evar_concl evi)) in
(*  msgnl(str"cherche "++pr_constr ev_typ++str" pour "++Util.pr_int ev);*)
  let substs = ref SubstSet.empty in
  try List.iter
    ( fun (gr,(pat,_),s) ->
	let (_,genl,_) = Termops.decompose_prod_letin pat in
	let genl = List.map (fun (_,_,t) -> t) genl in
	let ((cl,gen,evm),argl) = add_gen_ctx (cl,gen,evm) genl in
	let def = applistc (Libnames.constr_of_global gr) argl in
(*	msgnl(str"essayons  ?"++Util.pr_int ev++spc()++str":="++spc()
	      ++pr_constr def++spc()++str":"++spc()++pr_constr (Global.type_of_global gr)*)
	(*++spc()++str"dans"++spc()++pr_evar_map evm++spc());*)
	try
 	  let evm = safe_define evm ev def in
	  k (cl,gen,evm);
	  if sort_is_prop && SubstSet.mem s !substs then raise Exit;
	  substs := SubstSet.add s !substs
	with Termops.CannotFilter -> ()
    ) (Libtypes.search_concl ev_typ)
  with Exit -> ()

let evm_fold_rev f evm acc =
  let l = Evd.fold (fun ev evi acc -> (ev,evi)::acc) evm [] in
  List.fold_left (fun acc (ev,evi) -> f ev evi acc) acc l

exception Continue of Evd.evar * Evd.evar_info

(* searches matches for all the uninstantiated evars of evd in the
   context. For each totally instantiated evar_map found, apply
   k. *)
let rec complete_signature (k:signature -> unit) (cl,gen,evm:signature) =
  try
    evm_fold_rev
      ( fun ev evi _ ->
	  if not (is_defined evm ev) && not (List.mem ev gen) then
	    raise (Continue (ev,evi))
      ) evm (); k (cl,gen,evm)
  with Continue (ev,evi) -> complete_evar (cl,gen,evm) (ev,evi) (complete_signature k)

(* define all permutations of the evars to evd and call k on the
   resulting evd *)
let complete_with_evars_permut (cl,gen,evm:signature) evl c (k:signature -> unit) : unit =
  let rec aux evm = List.iter
    ( fun (ctx,ev) ->
	let tyl = List.map (fun (_,_,t) -> t) ctx in
	let ((cl,gen,evm),argl) = add_gen_ctx (cl,gen,evm) tyl in
	let def = applistc c argl in
(*	msgnl(str"trouvé def ?"++Util.pr_int ev++str" := "++pr_constr def++str " dans "++pr_evar_map evm);*)
	try
	  if not (Evd.is_defined evm ev) then
	    let evm = safe_define evm ev def in
	    aux evm; k (cl,gen,evm)
	with Termops.CannotFilter -> ()
    ) evl in
  aux evm

let new_inst_no =
  let cnt = ref 0 in
  fun () -> incr cnt; string_of_int !cnt

let make_instance_ident gr =
  Nameops.add_suffix (Nametab.basename_of_global gr) ("_autoinstance_"^new_inst_no())

let new_instance_message ident typ def =
  Flags.if_verbose
  msgnl (str"new instance"++spc()
	 ++Nameops.pr_id ident++spc()++str":"++spc()
	 ++pr_constr typ++spc()++str":="++spc()
	 ++pr_constr def)

open Entries

let rec deep_refresh_universes c =
  match kind_of_term c with
    | Sort (Type _) -> Termops.new_Type()
    | _ -> map_constr deep_refresh_universes c

let declare_record_instance gr ctx params =
  let ident = make_instance_ident gr in
  let def = it_mkLambda_or_LetIn (applistc (constr_of_global gr) params) ctx in
  let def = deep_refresh_universes def in
  let ce = { const_entry_body=def; const_entry_type=None;
	     const_entry_opaque=false; const_entry_boxed=false } in
  let cst = Declare.declare_constant ident
    (DefinitionEntry ce,Decl_kinds.IsDefinition Decl_kinds.StructureComponent) in
  new_instance_message ident (Typeops.type_of_constant (Global.env()) cst) def

let declare_class_instance gr ctx params =
  let ident = make_instance_ident gr in
  let cl = Typeclasses.class_info gr in
  let (def,typ) = Typeclasses.instance_constructor cl params in
  let (def,typ) = it_mkLambda_or_LetIn def ctx, it_mkProd_or_LetIn typ ctx in
  let def = deep_refresh_universes def in
  let typ = deep_refresh_universes typ in
  let ce = Entries.DefinitionEntry
    {  const_entry_type=Some typ; const_entry_body=def;
       const_entry_opaque=false; const_entry_boxed=false } in
  try
  let cst = Declare.declare_constant ident
    (ce,Decl_kinds.IsDefinition Decl_kinds.Instance) in
  Typeclasses.add_instance (Typeclasses.new_instance cl (Some 100) true (ConstRef cst));
  new_instance_message ident typ def
  with e -> msgnl (str"Error defining instance := "++pr_constr def++str" : "++pr_constr typ++str"  "++Cerrors.explain_exn e)

let rec iter_under_prod (f:rel_context->constr->unit) (ctx:rel_context) t = f ctx t;
  match kind_of_term t with
    | Prod (n,t,c) -> iter_under_prod f ((n,None,t)::ctx) c
    | _ -> ()

(* main search function: search for total instances containing gr, and
   apply k to each of them *)
let complete_signature_with_def gr deftyp (k:instance_decl_function -> signature -> unit) : unit =
  let gr_c = Libnames.constr_of_global gr in
  let (smap:(Libnames.global_reference * Evd.evar_map,
   ('a * 'b * Term.constr) list * Evd.evar)
  Gmapl.t ref) = ref Gmapl.empty in
  iter_under_prod
    ( fun ctx typ ->
	List.iter
	  (fun ((cl,ev,evm),_,_) ->
(*	     msgnl(pr_global gr++str" : "++pr_constr typ++str" matche ?"++Util.pr_int ev++str " dans "++pr_evar_map evm);*)
	     smap := Gmapl.add (cl,evm) (ctx,ev) !smap)
	  (Recordops.methods_matching typ)
    ) [] deftyp;
  Gmapl.iter
    ( fun (cl,evm) evl ->
	let f = if Typeclasses.is_class cl then
	  declare_class_instance else declare_record_instance in
	complete_with_evars_permut (cl,[],evm) evl gr_c
	  (fun sign -> complete_signature (k f) sign)
    ) !smap

(*
 * Interface with other parts: hooks & declaration
 *)


let evar_definition evi = match evar_body evi with
    Evar_empty -> assert false | Evar_defined c -> c

let gen_sort_topo l evm =
  let iter_evar f ev =
    let rec aux c = match kind_of_term c with
	Evar (e,_) -> f e
      | _ -> iter_constr aux c in
    aux (Evd.evar_concl (Evd.find evm ev));
    if Evd.is_defined evm ev then aux (evar_definition (Evd.find evm ev)) in
  let r = ref [] in
  let rec dfs ev = iter_evar dfs ev;
    if not(List.mem ev !r) then r := ev::!r in
  List.iter dfs l; List.rev !r

(* register real typeclass instance given a totally defined evd *)
let declare_instance (k:global_reference -> rel_context -> constr list -> unit)
    (cl,gen,evm:signature) =
  let evm = Evarutil.nf_evars evm in
  let gen = gen_sort_topo gen evm in
  let (evm,gen) = List.fold_right
    (fun ev (evm,gen) ->
       if Evd.is_defined evm ev
       then Evd.remove evm ev,gen
       else evm,(ev::gen))
    gen (evm,[]) in
(*  msgnl(str"instance complète : ["++Util.prlist_with_sep (fun _ -> str";") Util.pr_int gen++str"] : "++spc()++pr_evar_map evm);*)
  let ngen = List.length gen in
  let (_,ctx,evm) = List.fold_left
    ( fun (i,ctx,evm) ev ->
	let ctx = (Anonymous,None,lift (-i) (Evd.evar_concl(Evd.find evm ev)))::ctx in
	let evm = subst_evar_in_evm ev (mkRel i) (Evd.remove evm ev) in
	(i-1,ctx,evm)
    ) (ngen,[],evm) gen in
  let fields = List.rev (Evd.fold ( fun ev evi l -> evar_definition evi::l ) evm []) in
  k cl ctx fields

let autoinstance_opt = ref true

let search_declaration gr =
  if !autoinstance_opt &&
    not (Lib.is_modtype()) then
    let deftyp = Global.type_of_global gr in
    complete_signature_with_def gr deftyp declare_instance

let search_record k cons sign =
  if !autoinstance_opt && not (Lib.is_modtype()) then
    complete_signature (declare_instance k) (cons,[],sign)

(*
let dh_key = Profile.declare_profile "declaration_hook"
let ch_key = Profile.declare_profile "class_decl_hook"
let declaration_hook = Profile.profile1 dh_key declaration_hook
let class_decl_hook = Profile.profile1 ch_key class_decl_hook
*)

(*
 *  Options and bookeeping
 *)

let begin_autoinstance () =
  if not !autoinstance_opt then (
    autoinstance_opt := true;
  )

let end_autoinstance () =
  if !autoinstance_opt then (
    autoinstance_opt := false;
 )

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync=true;
      Goptions.optkey=["Autoinstance"];
      Goptions.optname="automatic typeclass instance recognition";
      Goptions.optread=(fun () -> !autoinstance_opt);
      Goptions.optwrite=(fun b -> if b then begin_autoinstance() else end_autoinstance()) }
