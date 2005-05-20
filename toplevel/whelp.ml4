(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Options
open Pp
open Util
open System
open Names
open Term
open Environ
open Rawterm
open Libnames
open Nametab
open Constrintern
open Dischargedhypsmap
open Command
open Detyping

(* Coq interface to the Whelp query engine developed at 
   the University of Bologna *)

let make_whelp_request req c =
  "http://mowgli.cs.unibo.it/forward/58080/apply?xmluri=http%3A%2F%2Fmowgli.cs.unibo.it%3A58081%2Fgetempty&param.profile=firewall&profile=firewall&param.keys=d_c%2CC1%2CHC2%2CL&param.embedkeys=d_c%2CTC1%2CHC2%2CL&param.thkeys=T1%2CT2%2CL%2CE&param.prooftreekeys=HAT%2CG%2CHAO%2CL&param.media-type=text%2Fhtml&param.thmedia-type=&prooftreemedia-type=&param.doctype-public=&param.encoding=&param.thencoding=&param.prooftreeencoding=&advanced=no&keys=S%2CT1%2CT2%2CL%2CRT%2CE&param.expression=" ^ c ^ "&param.action=" ^ req

let uri_of_dirpath dir =
  "cic:/" ^ String.concat "/" (List.map Names.string_of_id (List.rev dir))

let error_whelp_unknown_reference ref =
  let qid = Nametab.shortest_qualid_of_global Idset.empty ref in
  error ("Unknown Whelp reference: " ^ string_of_qualid qid)

let uri_of_repr_kn ref (mp,dir,l) = 
  match mp with
    | MPfile sl ->
        uri_of_dirpath (id_of_label l :: repr_dirpath dir @ repr_dirpath sl)
    | _ ->
        error_whelp_unknown_reference ref

let url_encode_product = "%5Cforall+" (* \forall *)
let url_encode_imply  = "%5Cto+"      (* \to *)
let url_encode_lambda  = "%5Clambda+" (* \lambda *)
let url_encode_let = "let+"           (* let *)
let url_encode_def = "%5Cdef+"        (* \def *)
let url_encode_in = "+in+"            (* in *)
let url_encode_colon = "%3A"          (* : *)
let url_encode_dot = "."              (* . *)
let url_encode_semicolon = "%3B"      (* ; *)
let uri_encode_question_mark = "%3F"  (* ? *)
let url_encode_lpar = "%28"           (* ( *)
let url_encode_rpar = "%29"           (* ) *)
let url_encode_slash = "%2F"          (* / *)
let url_encode_subst = "%5Csubst"     (* \subst *)
let url_encode_assign = "%5CAssign"   (* \Assign *)
let url_encode_ind_pointer = ".ind%23xpointer" (* .ind#xpointer *)
let url_paren s = url_encode_lpar ^ s ^ url_encode_rpar
let url_bracket s = "%5B" ^ s ^ "%5D"

let uri_of_sort = function
  | RProp Null -> "Prop"
  | RProp Pos -> "Set"
  | RType _ -> "Type"

let uri_of_global ref =
  match ref with
  | VarRef id -> error "Unknown Whelp reference: "^(string_of_id id)
  | ConstRef cst ->
      uri_of_repr_kn ref (repr_con cst)
      ^".con"
  | IndRef (kn,i) -> 
      uri_of_repr_kn ref (repr_kn kn) ^ url_encode_ind_pointer ^
      url_paren ("1" ^ url_encode_slash ^ string_of_int (i+1))
  | ConstructRef ((kn,i),j) ->
      uri_of_repr_kn ref (repr_kn kn) ^ url_encode_ind_pointer ^
      url_paren ("1" ^ url_encode_slash ^ string_of_int (i+1)
                     ^ url_encode_slash ^ string_of_int j)

let whelm_special = id_of_string "WHELM_ANON_VAR"

let url_of_name = function
  | Name id -> string_of_id id
  | Anonymous -> string_of_id whelm_special (* No anon id in Whelp *)

let uri_of_binding (id,c) = string_of_id id ^ url_encode_assign ^ c

let uri_params = function
  | [] -> ""
  | l -> url_encode_subst ^ url_bracket 
      (String.concat url_encode_semicolon (List.map uri_of_binding l))

let get_discharged_hyp_names sp = List.map basename (get_discharged_hyps sp)

let section_parameters = function
  | RRef (_,(ConstructRef ((induri,_),_) | IndRef (induri,_))) ->
      get_discharged_hyp_names (sp_of_global (IndRef(induri,0)))
  | RRef (_,(ConstRef cst as ref)) ->
      get_discharged_hyp_names (sp_of_global ref)
  | _ -> []

let merge vl al =
  let rec aux acc = function
  | ([],l) | (_,([] as l)) -> List.rev acc, l
  | (v::vl,a::al) -> aux ((v,a)::acc) (vl,al)
  in aux [] (vl,al)

let rec uri_of_constr = function
  | RVar (_,id) -> string_of_id id
  | RRef (_,ref) -> (uri_of_global ref)
  | RApp (_,f,args) ->
      let args = List.map uri_of_constr args in
      let inst,rest = merge (section_parameters f) args in
      url_paren (uri_of_constr f ^ "+" ^ uri_params inst ^ 
        String.concat "+" rest)
  | RLambda (_,na,ty,c) ->
      url_paren (url_encode_lambda ^ url_of_name na ^ url_encode_colon
        ^ uri_of_constr ty ^ url_encode_dot ^ uri_of_constr c)
  | RProd (_,Anonymous,ty,c) ->
      url_paren (uri_of_constr ty ^ url_encode_imply ^ uri_of_constr c)
  | RProd (_,Name id,ty,c) ->
      url_paren (url_encode_product ^ string_of_id id ^ url_encode_colon
        ^ uri_of_constr ty ^ url_encode_dot ^ uri_of_constr c)
  | RLetIn (_,na,b,c) ->
      url_paren (url_encode_let ^ url_of_name na ^ url_encode_def ^ 
      uri_of_constr b ^ url_encode_in ^ uri_of_constr c)
  | RCast (_,c,t) ->
      url_paren (uri_of_constr c ^ url_encode_colon ^ uri_of_constr t)
  | RHole _ | REvar _ -> uri_encode_question_mark
  | RSort (_,s) -> uri_of_sort s
  | RRec _ | RIf _ | RLetTuple _ | ROrderedCase _ | RCases _ ->
      error "Whelp does not support pattern-matching and (co-)fixpoint"
  | RPatVar _ | RDynamic _ -> 
      anomaly "Found constructors not supported in constr"

let send_whelp req s =
  let url = make_whelp_request req s in
  let command = (fst browser_cmd_fmt) ^ url ^ (snd browser_cmd_fmt) in
  let _ = run_command (fun x -> x) print_string command in ()

let whelp_constr env req c =
  let c = detype (false,env) [whelm_special] [] c in
  send_whelp req (uri_of_constr c)

let whelp_constr_expr req c =
  let (sigma,env)= get_current_context () in
  let _,c = interp_openconstr_gen sigma env ([],[]) c None in
  whelp_constr env req c

let whelp_locate s =
  send_whelp "locate" s

let whelp_elim ind =
  send_whelp "elim" 
(*    (uri_of_global (IndRef ind))*)
    (string_of_qualid (shortest_qualid_of_global Idset.empty (IndRef ind)))

let locate_inductive r =
  let (loc,qid) = qualid_of_reference r in
  try match Syntax_def.locate_global qid with
    | IndRef ind -> ind
    | _ -> user_err_loc (loc,"",str "Inductive type expected")
  with Not_found -> error_global_not_found_loc loc qid

type whelp_request =
  | Locate of string
  | Elim of inductive
  | Constr of string * env * constr

let whelp = function
  | Locate s -> whelp_locate s
  | Elim ind -> whelp_elim ind
  | Constr (s,env,c) -> whelp_constr env s c

VERNAC ARGUMENT EXTEND whelp_constr_request
| [ "Match" ] -> [ "match" ]
| [ "Hint" ] -> [ "hint" ]
| [ "Instance" ] -> [ "instance" ]
END

VERNAC COMMAND EXTEND Whelp
| [ "Whelp" "Locate" string(s) ] -> [ whelp_locate s ] 
| [ "Whelp" "Elim" global(r) ] -> [ whelp_elim (locate_inductive r) ] 
| [ "Whelp" whelp_constr_request(req) constr(c) ] -> [ whelp_constr_expr req c]
END
