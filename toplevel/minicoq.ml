(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Identifier
open Names
open Term
open Sign
open Declarations
open Mod_declarations
open Inductive
open Indtypes
open Type_errors
open Safe_env
open G_minicoq

let (env : safe_environment ref) = ref empty_environment

let (scopes : module_path Stringmap.t list ref) = ref []
let (scope : module_path Stringmap.t ref) = ref Stringmap.empty

let (modpath : module_path ref) = ref top_path

(*let locals () =
  List.map (fun (id,b,t) -> (id, make_path [] id CCI))
    (named_context !env) *)


let (dict : constr Idmap.t ref) = ref Idmap.empty

let split s = 
  let rec search i = 
    try 
      let j = String.index_from s i '.' in
	String.sub s i (j-i)::(search (j+1))
    with 
      | Not_found -> [String.sub s i ((String.length s)-i)]
  in
    search 0

let scope_string s scope = 
  let strlist = split s in
  let mp = Stringmap.find (List.hd strlist) scope in
  let rec fold_modpath mp = function 
    | [] -> mp
    | s::rest -> fold_modpath (MPdot(mp, (label_of_string s))) rest
  in
    fold_modpath mp (List.tl strlist)
      
let scope_ln ln scope = 
  let MPdot(mp,l) = 
    scope_string (string_of_label (label ln)) scope 
  in
    make_ln mp l

let scope_mp (MPdot(_,l)) = scope_string (string_of_label l)
  
  
let lookup_named id =
  let rec look n = function
    | [] -> (try Idmap.find id !dict with Not_found -> mkVar id)
    | (Name id')::_ when id = id' -> mkRel n
    | _::r -> look (succ n) r
  in
  look 1

(*let args sign = Array.of_list (instance_from_section_context sign)*)

let rec globalize scope bv c = match kind_of_term c with
  | IsVar id -> lookup_named id bv
  | IsConst (ln, _) ->
      let ln = scope_ln ln scope in
	mkConst (ln, [| |])
  | IsMutInd ((ln,i), _) ->
      let ln = scope_ln ln scope in
	mkMutInd ((ln,i), [| |])
  | IsMutConstruct ((ln,i),j as spc, _) ->
      let ln = scope_ln ln scope in
	mkMutConstruct (((ln,i),j), [| |])
  | _ -> map_constr_with_named_binders (fun na l -> na::l) (globalize scope) bv c

(*let variable id t =
  let t = globalize [] t in
  env := push_named_assum (id,t) !env;
  mSGNL (hOV 0 [< 'sTR"variable"; 'sPC; pr_id id; 
		  'sPC; 'sTR"is declared"; 'fNL >])
*)

let const scope ce =
  { const_entry_body = option_app (globalize scope []) ce.const_entry_body;
    const_entry_type = option_app (globalize scope []) ce.const_entry_type }
  
let mind scope mie = 
  let par = (List.hd mie.mind_entry_inds).mind_entry_params in
  let bvpar = List.map (fun (id,_) -> Name id) par in
  let name_inds = 
    List.map 
      (fun oin -> Name (ident_of_label oin.mind_entry_typename))
      mie.mind_entry_inds
  in
  let bv = bvpar @ List.rev name_inds in
  let _,npar = 
    List.fold_right 
      (fun (id,LocalAssum c) (bv,pars) -> 
	 ((Name id)::bv, (id,LocalAssum (globalize scope bv c))::pars)) 
      par ([],[])
  in
  let one_inductive oin =
    { mind_entry_nparams = oin.mind_entry_nparams;
      mind_entry_params = npar;
      mind_entry_typename = oin.mind_entry_typename;
      mind_entry_arity = globalize scope bvpar oin.mind_entry_arity;
      mind_entry_consnames = oin.mind_entry_consnames;
      mind_entry_lc = List.map (globalize scope bv) oin.mind_entry_lc}
  in
    { mind_entry_finite = mie.mind_entry_finite;
      mind_entry_inds = List.map one_inductive mie.mind_entry_inds }
    
let rec module_expr scope = function
  | MEident mp -> MEident (scope_mp mp scope)
  | MEapply(mexpr1,mexpr2) -> 
      MEapply (module_expr scope mexpr1,module_expr scope mexpr2)
  | MEfunctor(mbid, mty, mexpr) ->
      let mty = modtype scope mty in
      let scope = 
	Stringmap.add 
	  (string_of_mbid mbid) 
	  (MPbid mbid) 
	  scope 
      in
      let mexpr = module_expr scope mexpr in
	MEfunctor(mbid,mty,mexpr)
  | MEstruct(msid,entries) ->
      let _,entries = 
	list_fold_map (lab_entry (MPsid msid)) scope entries 
      in
	MEstruct(msid,entries)

and modtype scope = function
  | MTEident ln -> MTEident (scope_ln ln scope)
  | MTEfunsig(mbid, arg_t, body_t) ->
      let arg_t = modtype scope arg_t in
      let scope = 
	Stringmap.add 
	  (string_of_mbid mbid) 
	  (MPbid mbid) 
	  scope 
      in
      let body_t = modtype scope body_t in
	MTEfunsig(mbid, arg_t, body_t) 
  | MTEsig(msid,entries) ->
      let _,entries = 
	list_fold_map (lab_entry (MPsid msid)) scope entries 
      in
	MTEsig(msid,entries)

and modul scope me =
  { mod_entry_type = option_app (modtype scope) me.mod_entry_type;
    mod_entry_expr = option_app (module_expr scope) me.mod_entry_expr }

and lab_entry mp scope = function
  | l,SPEconst ce -> 
      Stringmap.add (string_of_label l) (MPdot(mp,l)) scope, 
      (l, SPEconst(const scope ce))
  | l,SPEmind mie -> 
      Stringmap.add (string_of_label l) (MPdot(mp,l)) scope, 
      (l, SPEmind(mind scope mie))
  | l,SPEmodule me ->
      Stringmap.add (string_of_label l) (MPdot(mp,l)) scope, 
      (l,SPEmodule (modul scope me))
  | l,SPEmodtype mt ->
      Stringmap.add (string_of_label l) (MPdot(mp,l)) scope, 
      (l,SPEmodtype (modtype scope mt))

let add_entry = function
  | newscope, (l,SPEconst ce) -> 
      let newenv,ln = add_constant l ce !env in
      env := newenv;
      scope := newscope; 
      dict := Idmap.add 
	        (ident_of_label l) 
	        (mkConst (ln,[| |])) 
	        !dict; 
      mSGNL (hOV 0 [< 'sTR "Constant "; pr_label l; 'sPC; 'sTR"is defined"; 'fNL >])
  | newscope, (l,SPEmind mie) -> 
      let newenv,ln = add_mind mie !env in
      env := newenv;
      scope := newscope; 
      if List.length mie.mind_entry_inds = 1 then begin
	let [p] = mie.mind_entry_inds in
	let inductive = ln,0 in
	let dict' = Idmap.add 
	              (ident_of_label p.mind_entry_typename) 
	              (mkMutInd (inductive,[| |]))
	              !dict
        in

	  dict := list_fold_left_i
	    (fun i dict l ->
	       Idmap.add 
	        (ident_of_label l) 
	        (mkMutConstruct ((inductive,i),[| |]))
	        dict)
            1 
            dict'
            p.mind_entry_consnames
      end;
      mSGNL (hOV 0 [< 'sTR"inductive type(s) are declared"; 'fNL >])
  | newscope, (l,SPEmodule me) ->
      let newenv,_ = add_module l me !env in
      env := newenv;
      scope := newscope; 
      mSGNL (hOV 0 [< 'sTR"Module ";pr_label l; 'sTR" declared"; 'fNL >])
  | newscope, (l,SPEmodtype mt) ->
      let newenv,_ = add_modtype l mt !env in
      env := newenv;
      scope := newscope; 
      mSGNL (hOV 0 [< 'sTR"Module type ";pr_label l;'sTR " declared"; 'fNL >])

let begin_module l args mty_o = 
  let mod_binding scope (mbid, mty) =
    let mty = modtype scope mty in
    let scope = 
      Stringmap.add 
	(string_of_mbid mbid) 
	(MPbid mbid) 
	scope 
    in
      scope, (mbid, mty)
  in
  let newscope,args = list_fold_map mod_binding !scope args in
  let mty_o = option_app (modtype newscope) mty_o in
    env := begin_module l args mty_o !env;
    scopes := !scope::!scopes;
    scope := newscope;
    modpath := current_modpath (!env);
    mSGNL (hOV 0 [< 'sTR"New module is opened"; 'fNL >])
      

let end_module l = 
  let newenv,mp,_ = end_module l !env in
    env := newenv;
    modpath := current_modpath (!env);
    let newscope = 
      Stringmap.add 
	(string_of_label l) 
	mp
	(List.hd !scopes)
    in
      scope := newscope;
      scopes := List.tl !scopes;
      mSGNL (hOV 0 [< 'sTR"Module declared"; 'fNL >])
    

let check c = 
  let c = globalize !scope [] c in
  let (j,u) = safe_infer !env c in
  let ty = j_type j in
  let pty = pr_term (env_of_safe_env !env) ty in
  mSGNL (hOV 0 [< 'sTR"  :"; 'sPC; hOV 0 pty; 'fNL >])

let print ln = 
  let ln = scope_ln ln !scope in
  let cb = Safe_env.lookup_constant ln !env in
  let ty = out_some cb.const_body in
  let pty = pr_term (env_of_safe_env !env) ty in
  mSGNL (hOV 0 [< 'sTR"  :="; 'sPC; hOV 0 pty; 'fNL >])

let reduce c = 
  let c = globalize !scope [] c in
  let ty = Reduction.whd_betadeltaiota(*nf_betadeltaiota *)
	     (Safe_env.env_of_safe_env !env)
	     Evd.empty
             c
  in
  let pty = pr_term (env_of_safe_env !env) ty in
  mSGNL (hOV 0 [< 'sTR"  -->"; 'sPC; hOV 0 pty; 'fNL >])

let execute = function
  | Abbrev (s,c) -> 
      let c = globalize !scope [] c in
	dict:=Idmap.add s c !dict;
	mSGNL (hOV 0 [< 'sTR"Abbreviation added"; 'fNL >])
  | Check c -> check c
  | Print ln -> print ln
  | Reduce c -> reduce c
  | BeginModule (l, args, mty_o) -> begin_module l args mty_o
  | EndModule l -> end_module l
  | Entry e -> add_entry (lab_entry !modpath !scope e);;
(*  | Definition (id, ty, c) -> definition id ty c 
  | Parameter (id, t) -> parameter id t 
  | Variable (id, t) -> variable id t
  | Inductive (par,inds) -> inductive par inds
*)

let parse_file f =
  let c = open_in f in
  let cs = Stream.of_channel c in
  try
    while true do
      let c = Grammar.Entry.parse command cs in execute c
    done
  with 
    | End_of_file | Stdpp.Exc_located (_, End_of_file) -> close_in c; exit 0
    | exn -> close_in c; raise exn

module Explain = Fhimsg.Make(struct let pr_term = pr_term end)

let rec explain_exn = function
  | TypeError (ctx,te) -> 
      mSGNL (hOV 0 [< 'sTR "type error:"; 'sPC; 
		      Explain.explain_type_error ctx te; 'fNL >])
  | InductiveError err -> 
      mSGNL (hOV 0 [< 'sTR "inductive error:"; 'sPC;
		      Explain.explain_inductive_error err; 'fNL >])
  | Stdpp.Exc_located (_,exn) -> 
      explain_exn exn
  | Sys.Break -> raise Exit
  | exn -> 
      mSGNL (hOV 0 [< 'sTR"error: "; 'sTR (Printexc.to_string exn); 'fNL >])

let top () =
  let cs = Stream.of_channel stdin in
  while true do
    try
      let c = Grammar.Entry.parse command cs in execute c
    with 
      | End_of_file | Stdpp.Exc_located (_, End_of_file) -> raise Exit 
      | exn -> explain_exn exn
  done

let loop () = 
  let cs = Stream.of_channel stdin in
  while true do
    let c = Grammar.Entry.parse command cs in execute c
  done

let main () =
  if Array.length Sys.argv = 1 then
    parse_file "test"
  else
    if Sys.argv.(1) = "-top" then top () else parse_file (Sys.argv.(1))

let print_id id = Format.print_string (Identifier.string_of_id id);;
let print_lab lab = Format.print_string (Identifier.string_of_label lab);;
let print_constr c = pP (G_minicoq.pr_term (Safe_env.env_of_safe_env !env) c);;
(*let print_env env = Environ.fold_rel_context (fun _ (n,_,c) _ -> ((match n with Anonymous -> print_string "_" | Name id -> print_id id); print_string " : "; print_constr c; print_string ";")) env ();;*)

let _ = Printexc.print main ()

