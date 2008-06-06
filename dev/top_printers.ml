(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Printers for the ocaml toplevel. *)

open System
open Util
open Pp
open Names
open Libnames
open Nameops
open Sign
open Univ
open Proof_trees
open Environ
open Printer
open Tactic_printer
open Refiner
open Term
open Termops
open Clenv
open Cerrors
open Evd
open Goptions
open Genarg


let _ = Constrextern.print_evar_arguments := true
let _ = set_bool_option_value (SecondaryTable ("Printing","Matching")) false
let _ = Detyping.set_detype_anonymous (fun _ _ -> raise Not_found)

(* std_ppcmds *)
let pppp x = pp x

(* name printers *)
let ppid id = pp (pr_id id)
let pplab l = pp (pr_lab l)
let ppmsid msid = pp (str (debug_string_of_msid msid))
let ppmbid mbid = pp (str (debug_string_of_mbid mbid))
let ppdir dir = pp (pr_dirpath dir)
let ppmp mp = pp(str (string_of_mp mp))
let ppcon con = pp(pr_con con)
let ppkn kn = pp(pr_kn kn)
let ppsp sp = pp(pr_sp sp)
let ppqualid qid = pp(pr_qualid qid)
let ppclindex cl = pp(Classops.pr_cl_index cl)

(* term printers *)
let rawdebug = ref false
let ppconstr x = pp (Termops.print_constr x)
let ppconstrdb x = pp(Flags.with_option rawdebug Termops.print_constr x)
let ppterm = ppconstr
let ppsconstr x = ppconstr (Declarations.force x)
let ppconstr_univ x = Constrextern.with_universes ppconstr x
let pprawconstr = (fun x -> pp(pr_lrawconstr x))
let pppattern = (fun x -> pp(pr_constr_pattern x))
let pptype = (fun x -> pp(pr_ltype x))

let ppfconstr c = ppconstr (Closure.term_of_fconstr c)

let ppbigint n = pp (Bigint.pr_bigint n);;

let prset pr l = str "[" ++ prlist_with_sep spc pr l ++ str "]"
let ppintset l = pp (prset int (Intset.elements l))
let ppidset l = pp (prset pr_id (Idset.elements l))

let pP s = pp (hov 0 s)

let safe_pr_global = function 
  | ConstRef kn -> pp (str "CONSTREF(" ++ pr_con kn ++ str ")")
  | IndRef (kn,i) -> pp (str "INDREF(" ++ pr_kn kn ++ str "," ++ 
			  int i ++ str ")")
  | ConstructRef ((kn,i),j) -> pp (str "INDREF(" ++ pr_kn kn ++ str "," ++ 
				      int i ++ str "," ++ int j ++ str ")")
  | VarRef id -> pp (str "VARREF(" ++ pr_id id ++ str ")")

let ppglobal x = try pp(pr_global x) with _ -> safe_pr_global x

let ppconst (sp,j) =
    pp (str"#" ++ pr_kn sp ++ str"=" ++ pr_lconstr j.uj_val)

let ppvar ((id,a)) =
    pp (str"#" ++ pr_id id ++ str":" ++ pr_lconstr a)

let genppj f j = let (c,t) = f j in (c ++ str " : " ++ t)

let ppj j = pp (genppj pr_ljudge j)

let prsubst s = pp (Mod_subst.debug_pr_subst s)

let pp_idpred s = pp (pr_idpred s)
let pp_cpred s = pp (pr_cpred s)
let pp_transparent_state s = pp (pr_transparent_state s)

(* proof printers *)
let ppmetas metas = pp(pr_metaset metas)
let ppevm evd = pp(pr_evar_map evd)
let ppevd evd = pp(pr_evar_defs evd)
let ppclenv clenv = pp(pr_clenv clenv)
let ppgoal g = pp(db_pr_goal g)

let pr_gls gls =
  hov 0 (pr_evar_map (sig_sig gls) ++ fnl () ++ db_pr_goal (sig_it gls))

let pr_glls glls =
  hov 0 (pr_evar_map (sig_sig glls) ++ fnl () ++
         prlist_with_sep pr_fnl db_pr_goal (sig_it glls))

let ppsigmagoal g = pp(pr_goal (sig_it g))
let prgls gls = pp(pr_gls gls)
let prglls glls = pp(pr_glls glls)
let pproof p = pp(print_proof Evd.empty empty_named_context p)

let ppuni u = pp(pr_uni u)

let ppuniverses u = pp (str"[" ++ pr_universes u ++ str"]")

let ppconstraints c = pp (pr_constraints c)

let ppenv e = pp
  (str "[" ++ pr_named_context_of e ++ str "]" ++ spc() ++
   str "[" ++ pr_rel_context e (rel_context e) ++ str "]")

let pptac = (fun x -> pp(Pptactic.pr_glob_tactic (Global.env()) x))

let ppobj obj = Format.print_string (Libobject.object_tag obj)

let cnt = ref 0

let cast_kind_display k = 
  match k with
  | VMcast -> "VMcast"
  | DEFAULTcast -> "DEFAULTcast"

let constr_display csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> "Rel("^(string_of_int n)^")"
  | Meta n -> "Meta("^(string_of_int n)^")"
  | Var id -> "Var("^(string_of_id id)^")"
  | Sort s -> "Sort("^(sort_display s)^")"
  | Cast (c,k, t) -> 
      "Cast("^(term_display c)^","^(cast_kind_display k)^","^(term_display t)^")"
  | Prod (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | Lambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | LetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | App (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
  | Evar (e,l) -> "Evar("^(string_of_int e)^","^(array_display l)^")"
  | Const c -> "Const("^(string_of_con c)^")"
  | Ind (sp,i) ->
      "MutInd("^(string_of_kn sp)^","^(string_of_int i)^")"
  | Construct ((sp,i),j) ->
      "MutConstruct(("^(string_of_kn sp)^","^(string_of_int i)^"),"
      ^(string_of_int j)^")"
  | Case (ci,p,c,bl) ->
      "MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
      ^(array_display bl)^")"
  | Fix ((t,i),(lna,tl,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^",[|"
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^"|],"
      ^(array_display bl)^")"
  | CoFix(i,(lna,tl,bl)) ->
      "CoFix("^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"

  and array_display v =
    "[|"^
    (Array.fold_right
       (fun x i -> (term_display x)^(if not(i="") then (";"^i) else ""))
       v "")^"|]"

  and sort_display = function
    | Prop(Pos) -> "Prop(Pos)"
    | Prop(Null) -> "Prop(Null)"
    | Type u ->
	incr cnt; pp (str "with " ++ int !cnt ++ pr_uni u ++ fnl ());
	"Type("^(string_of_int !cnt)^")"

  and name_display = function
    | Name id -> "Name("^(string_of_id id)^")"
    | Anonymous -> "Anonymous"

  in
    msg (str (term_display csr) ++fnl ())

open Format;;

let print_pure_constr csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> print_string "#"; print_int n
  | Meta n -> print_string "Meta("; print_int n; print_string ")"
  | Var id -> print_string (string_of_id id)
  | Sort s -> sort_display s
  | Cast (c,_, t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | Prod (Name(id),t,c) ->
      open_hovbox 1;
      print_string"("; print_string (string_of_id id); 
      print_string ":"; box_display t; 
      print_string ")"; print_cut(); 
      box_display c; close_box()
  | Prod (Anonymous,t,c) ->
      print_string"("; box_display t; print_cut(); print_string "->";
      box_display c; print_string ")"; 
  | Lambda (na,t,c) ->
      print_string "["; name_display na;
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c; 
  | LetIn (na,b,t,c) ->
      print_string "["; name_display na; print_string "="; 
      box_display b; print_cut();
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c; 
  | App (c,l) -> 
      print_string "("; 
      box_display c; 
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string ")"
  | Evar (e,l) -> print_string "Evar#"; print_int e; print_string "{";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | Const c -> print_string "Cons(";
      sp_con_display c;
      print_string ")"
  | Ind (sp,i) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string ")"
  | Construct ((sp,i),j) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j; print_string ")"
  | Case (ci,p,c,bl) ->
      open_vbox 0;
      print_string "<"; box_display p; print_string ">";
      print_cut(); print_string "Case";
      print_space(); box_display c; print_space (); print_string "of";
      open_vbox 0;
      Array.iter (fun x ->  print_cut();  box_display x) bl;
      close_box();
      print_cut(); 
      print_string "end"; 
      close_box()
  | Fix ((t,i),(lna,tl,bl)) ->
      print_string "Fix("; print_int i; print_string ")"; 
      print_cut();
      open_vbox 0;
      let rec print_fix () =
        for k = 0 to (Array.length tl) - 1 do
	  open_vbox 0;
	  name_display lna.(k); print_string "/"; 
	  print_int t.(k); print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut()
        done
      in print_string"{"; print_fix(); print_string"}" 
  | CoFix(i,(lna,tl,bl)) ->
      print_string "CoFix("; print_int i; print_string ")"; 
      print_cut();
      open_vbox 0;
      let rec print_fix () =
        for k = 0 to (Array.length tl) - 1 do
          open_vbox 1;
	  name_display lna.(k);  print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut();
        done
      in print_string"{"; print_fix (); print_string"}"

  and box_display c = open_hovbox 1; term_display c; close_box()

  and sort_display = function
    | Prop(Pos) -> print_string "Set"
    | Prop(Null) -> print_string "Prop"
    | Type u -> open_hbox();
	print_string "Type("; pp (pr_uni u); print_string ")"; close_box()

  and name_display = function
    | Name id -> print_string (string_of_id id)
    | Anonymous -> print_string "_"
(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display sp = 
(*    let dir,l = decode_kn sp in
    let ls = 
      match List.rev (List.map string_of_id (repr_dirpath dir)) with 
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l 
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (string_of_kn sp)
  and sp_con_display sp = 
(*    let dir,l = decode_kn sp in
    let ls = 
      match List.rev (List.map string_of_id (repr_dirpath dir)) with 
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l 
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (string_of_con sp)

  in
    try 
     box_display csr; print_flush()
    with e ->
	print_string (Printexc.to_string e);print_flush ();
	raise e

let ppfconstr c = ppconstr (Closure.term_of_fconstr c)

let pploc x = let (l,r) = unloc x in
  print_string"(";print_int l;print_string",";print_int r;print_string")"

(* extendable tactic arguments *)
let rec pr_argument_type = function
  (* Basic types *)
  | BoolArgType -> str"bool"
  | IntArgType -> str"int"
  | IntOrVarArgType -> str"int-or-var"
  | StringArgType -> str"string"
  | PreIdentArgType -> str"pre-ident"
  | IntroPatternArgType -> str"intro-pattern"
  | IdentArgType -> str"ident"
  | VarArgType -> str"var"
  | RefArgType -> str"ref"
  (* Specific types *)
  | SortArgType -> str"sort"
  | ConstrArgType -> str"constr"
  | ConstrMayEvalArgType -> str"constr-may-eval"
  | QuantHypArgType -> str"qhyp"
  | OpenConstrArgType _ -> str"open-constr"
  | ConstrWithBindingsArgType -> str"constr-with-bindings"
  | BindingsArgType -> str"bindings"
  | RedExprArgType -> str"redexp"
  | List0ArgType t -> pr_argument_type t ++ str" list0"
  | List1ArgType t -> pr_argument_type t ++ str" list1"
  | OptArgType t -> pr_argument_type t ++ str" opt"
  | PairArgType (t1,t2) ->
      str"("++ pr_argument_type t1 ++ str"*" ++ pr_argument_type t2 ++str")"
  | ExtraArgType s -> str"\"" ++ str s ++ str "\""

let pp_argument_type t = pp (pr_argument_type t)

let pp_generic_argument arg =
  pp(str"<genarg:"++pr_argument_type(genarg_tag arg)++str">")

(**********************************************************************)
(* Vernac-level debugging commands                                    *)

let in_current_context f c =
  let (evmap,sign) = 
    try Pfedit.get_current_goal_context ()
    with e when Logic.catchable_exception e -> (Evd.empty, Global.env()) in
  f (Constrintern.interp_constr evmap sign c)

(* We expand the result of preprocessing to be independent of camlp4

VERNAC COMMAND EXTEND PrintPureConstr
| [ "PrintPureConstr" constr(c) ] -> [ in_current_context print_pure_constr c ]
END
VERNAC COMMAND EXTEND PrintConstr
  [ "PrintConstr" constr(c) ] -> [ in_current_context constr_display c ]
END
*)

open Pcoq
open Genarg
open Egrammar

let _ =
  try
    Vernacinterp.vinterp_add "PrintConstr"
      (function
         [c] when genarg_tag c = ConstrArgType && true ->
           let c = out_gen rawwit_constr c in
           (fun () -> in_current_context constr_display c)
       | _ -> failwith "Vernac extension: cannot occur")
  with
    e -> Pp.pp (Cerrors.explain_exn e)
let _ =
  extend_vernac_command_grammar "PrintConstr"
    [[TacTerm "PrintConstr";
      TacNonTerm
        (dummy_loc,
         (Gramext.Snterm (Pcoq.Gram.Entry.obj Constr.constr),
          ConstrArgType),
         Some "c")]]

let _ =
  try
    Vernacinterp.vinterp_add "PrintPureConstr"
      (function
         [c] when genarg_tag c = ConstrArgType && true ->
           let c = out_gen rawwit_constr c in
           (fun () -> in_current_context print_pure_constr c)
       | _ -> failwith "Vernac extension: cannot occur")
  with
    e -> Pp.pp (Cerrors.explain_exn e)
let _ =
  extend_vernac_command_grammar "PrintPureConstr"
    [[TacTerm "PrintPureConstr";
      TacNonTerm
        (dummy_loc,
         (Gramext.Snterm (Pcoq.Gram.Entry.obj Constr.constr),
          ConstrArgType),
         Some "c")]]

(* Setting printer of unbound global reference *)
open Names
open Nameops
open Libnames

let encode_path loc prefix mpdir suffix id =
  let dir = match mpdir with
    | None -> []
    | Some (mp,dir) -> 
	(repr_dirpath (dirpath_of_string (string_of_mp mp))@
	repr_dirpath dir) in
  Qualid (loc, make_qualid 
    (make_dirpath (List.rev (id_of_string prefix::dir@suffix))) id)

let raw_string_of_ref loc = function
  | ConstRef cst -> 
      let (mp,dir,id) = repr_con cst in
      encode_path loc "CST" (Some (mp,dir)) [] (id_of_label id)
  | IndRef (kn,i) ->
      let (mp,dir,id) = repr_kn kn in
      encode_path loc "IND" (Some (mp,dir)) [id_of_label id] 
	(id_of_string ("_"^string_of_int i))
  | ConstructRef ((kn,i),j) -> 
      let (mp,dir,id) = repr_kn kn in
      encode_path loc "CSTR" (Some (mp,dir))
	[id_of_label id;id_of_string ("_"^string_of_int i)] 
	(id_of_string ("_"^string_of_int j))
  | VarRef id -> 
      encode_path loc "SECVAR" None [] id

let short_string_of_ref loc = function
  | VarRef id -> Ident (loc,id)
  | ConstRef cst -> Ident (loc,id_of_label (pi3 (repr_con cst)))
  | IndRef (kn,0) -> Ident (loc,id_of_label (pi3 (repr_kn kn)))
  | IndRef (kn,i) ->
      encode_path loc "IND" None [id_of_label (pi3 (repr_kn kn))]
        (id_of_string ("_"^string_of_int i))
  | ConstructRef ((kn,i),j) -> 
      encode_path loc "CSTR" None 
        [id_of_label (pi3 (repr_kn kn));id_of_string ("_"^string_of_int i)]
        (id_of_string ("_"^string_of_int j))

let _ = Constrextern.set_debug_global_reference_printer
  (if !rawdebug then raw_string_of_ref else short_string_of_ref)
