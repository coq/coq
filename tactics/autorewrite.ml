open Ast
open Coqast
open Equality
open Hipattern
open Names
open Pp
open Proof_type
open Tacmach
open Tacinterp
open Tactics
open Term
open Util
open Vernacinterp

(* Rewriting rules *)
type rew_rule = constr * bool * tactic

(* Summary and Object declaration *)
let rewtab =
  ref ((Hashtbl.create 53) : (string,rew_rule) Hashtbl.t)

let lookup id = Hashtbl.find id !rewtab

let _ = 
  let init () = rewtab := (Hashtbl.create 53) in
  let freeze () = !rewtab in
  let unfreeze fs = rewtab := fs in
  Summary.declare_summary "autorewrite"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_section   = false }

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = constr * bool * t

(* Applies all the rules of one base *)
let one_base tac_main bas =
  let lrul = Hashtbl.find_all !rewtab bas in
  if lrul = [] then
    errorlabstrm "AutoRewrite"
      [<'sTR ("Rewriting base "^(bas)^" does not exist") >]
  else
    tclREPEAT_MAIN (tclPROGRESS (List.fold_left (fun tac (csr,dir,tc) ->
      tclTHEN tac
      (if dir then tclREPEAT_MAIN (tclTHENST (rewriteLR csr) [tac_main] tc)
       else tclREPEAT_MAIN (tclTHENST (rewriteRL csr) [tac_main] tc))) 
      tclIDTAC lrul))

(* The AutoRewrite tactic *)
let autorewrite tac_main lbas =
  tclREPEAT_MAIN (tclPROGRESS
    (List.fold_left (fun tac bas -> 
       tclTHEN tac (one_base tac_main bas)) tclIDTAC lbas))

(* Functions necessary to the library object declaration *)
let load_hintrewrite _ = ()
let cache_hintrewrite (_,(rbase,lrl)) =
  List.iter
    (fun (c,b,t) -> Hashtbl.add !rewtab rbase (c,b,Tacinterp.interp t)) lrl
let export_hintrewrite x = Some x

(* Declaration of the Hint Rewrite library object *)
let (in_hintrewrite,out_hintrewrite)=
  Libobject.declare_object
    ("HINT_REWRITE",
     { Libobject.load_function = load_hintrewrite;
       Libobject.open_function = cache_hintrewrite;
       Libobject.cache_function = cache_hintrewrite;
       Libobject.export_function = export_hintrewrite })

(* To add rewriting rules to a base *)
let add_rew_rules base lrul =
  Lib.add_anonymous_leaf (in_hintrewrite (base,lrul))

(* The vernac declaration of HintRewrite *)
let _ = vinterp_add "HintRewrite"
  (function
    | [VARG_STRING ort;VARG_CONSTRLIST lcom;VARG_IDENTIFIER id;VARG_TACTIC t]
      when ort = "LR" || ort = "RL" ->
      (fun () ->
       let (evc,env) = Command.get_current_context () in
       let lcsr =
         List.map (function
	   | Node(loc,"CONSTR",l) ->
             constr_of_Constr (interp_tacarg
             (evc,env,[],[],None,Tactic_debug.DebugOff)
             (Node(loc,"COMMAND",l)))
           | _ -> bad_vernac_args "HintRewrite") lcom in
       add_rew_rules (string_of_id id)
         (List.map (fun csr -> (csr,ort = "LR",t)) lcsr))
    | _  -> bad_vernac_args "HintRewrite")

(* To get back the tactic arguments and call AutoRewrite *)
let v_autorewrite = function
  | (Tac (t,_))::l ->
    let lbas =
      List.map (function 
	| Identifier id -> string_of_id id
	| _ -> Tacinterp.bad_tactic_args "AutoRewrite") l in
    autorewrite t lbas
  | l ->
    let lbas = 
      List.map (function 
	| Identifier id -> string_of_id id
	| _ -> Tacinterp.bad_tactic_args "AutoRewrite") l in
    autorewrite tclIDTAC lbas

(* Declaration of AutoRewrite *)
let _ = hide_tactic "AutoRewrite" v_autorewrite
