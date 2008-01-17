(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Flags
open Pp
open Util
open System
open Names
open Term
open Environ
open Rawterm
open Libnames
open Nametab
open Termops
open Detyping
open Constrintern
open Dischargedhypsmap
open Command
open Syntax_def

(* arnaud: trucs factices *)
let nth_goal_of_pftreestate _ = Util.anomaly "Whelp.nth_goal_of_pftreestate: fantome"
let get_pftreestate _ = Util.anomaly "Whelp.get_pftreestate: fantome"
let pf_concl _ = Util.anomaly "Whelp.pf_concl: fantome"
let pf_hyps _ = Util.anomaly "Whelp.pf_hyps: fantome"


(* arnaud: /trucs factices *)

(* Coq interface to the Whelp query engine developed at 
   the University of Bologna *)

let whelp_server_name = ref "http://mowgli.cs.unibo.it:58080"
let getter_server_name = ref "http://mowgli.cs.unibo.it:58081"

open Goptions

let _ =
  declare_string_option 
    { optsync  = false;
      optname  = "Whelp server";
      optkey   = (SecondaryTable ("Whelp","Server"));
      optread  = (fun () -> !whelp_server_name);
      optwrite = (fun s -> whelp_server_name := s) }

let _ =
  declare_string_option 
    { optsync  = false;
      optname  = "Whelp getter";
      optkey   = (SecondaryTable ("Whelp","Getter"));
      optread  = (fun () -> !getter_server_name);
      optwrite = (fun s -> getter_server_name := s) }


let make_whelp_request req c =
  !whelp_server_name ^ "/apply?xmluri=" ^ !getter_server_name ^ "/getempty&param.profile=firewall&profile=firewall&param.keys=d_c%2CC1%2CHC2%2CL&param.embedkeys=d_c%2CTC1%2CHC2%2CL&param.thkeys=T1%2CT2%2CL%2CE&param.prooftreekeys=HAT%2CG%2CHAO%2CL&param.media-type=text%2Fhtml&param.thmedia-type=&prooftreemedia-type=&param.doctype-public=&param.encoding=&param.thencoding=&param.prooftreeencoding=&advanced=no&keys=S%2CT1%2CT2%2CL%2CRT%2CE&param.expression=" ^ c ^ "&param.action=" ^ req

let b = Buffer.create 16

let url_char c =
  if 'A' <= c & c <= 'Z' or 'a' <= c & c <= 'z' or 
     '0' <= c & c <= '9' or c ='.'
  then Buffer.add_char b c
  else Buffer.add_string b (Printf.sprintf "%%%2X" (Char.code c))

let url_string s = String.iter url_char s

let rec url_list_with_sep sep f = function
  | [] -> ()
  | [a] -> f a
  | a::l -> f a; url_string sep; url_list_with_sep sep f l 

let url_id id = url_string (string_of_id id)

let uri_of_dirpath dir =
  url_string "cic:/"; url_list_with_sep "/" url_id (List.rev dir)

let error_whelp_unknown_reference ref =
  let qid = Nametab.shortest_qualid_of_global Idset.empty ref in
  error ("Definitions of the current session not supported in Whelp: " ^ string_of_qualid qid)

let uri_of_repr_kn ref (mp,dir,l) = 
  match mp with
    | MPfile sl ->
        uri_of_dirpath (id_of_label l :: repr_dirpath dir @ repr_dirpath sl)
    | _ ->
        error_whelp_unknown_reference ref

let url_paren f l = url_char '('; f l; url_char ')'
let url_bracket f l = url_char '['; f l; url_char ']'

let whelp_of_rawsort = function
  | RProp Null -> "Prop"
  | RProp Pos -> "Set"
  | RType _ -> "Type"

let uri_int n = Buffer.add_string b (string_of_int n)

let uri_of_ind_pointer l =
  url_string ".ind#xpointer"; url_paren (url_list_with_sep "/" uri_int) l

let uri_of_global ref =
  match ref with
  | VarRef id -> error ("Unknown Whelp reference: "^(string_of_id id))
  | ConstRef cst ->
      uri_of_repr_kn ref (repr_con cst); url_string ".con"
  | IndRef (kn,i) -> 
      uri_of_repr_kn ref (repr_kn kn); uri_of_ind_pointer [1;i+1]
  | ConstructRef ((kn,i),j) ->
      uri_of_repr_kn ref (repr_kn kn); uri_of_ind_pointer [1;i+1;j]

let whelm_special = id_of_string "WHELM_ANON_VAR"

let url_of_name = function
  | Name id -> url_id id
  | Anonymous -> url_id whelm_special (* No anon id in Whelp *)

let uri_of_binding f (id,c) = url_id id; url_string "\\Assign "; f c

let uri_params f = function
  | [] -> ()
  | l -> url_string "\\subst"; 
         url_bracket (url_list_with_sep ";" (uri_of_binding f)) l

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

let rec uri_of_constr c =
  match c with
  | RVar (_,id) -> url_id id
  | RRef (_,ref) ->  uri_of_global ref
  | RHole _ | REvar _ -> url_string "?"
  | RSort (_,s) -> url_string (whelp_of_rawsort s)
  | _ -> url_paren (fun () -> match c with
  | RApp (_,f,args) ->
      let inst,rest = merge (section_parameters f) args in
      uri_of_constr f; url_char ' '; uri_params uri_of_constr inst; 
      url_list_with_sep " " uri_of_constr rest
  | RLambda (_,na,ty,c) ->
      url_string "\\lambda "; url_of_name na; url_string ":";
      uri_of_constr ty; url_string "."; uri_of_constr c
  | RProd (_,Anonymous,ty,c) ->
      uri_of_constr ty; url_string "\\to "; uri_of_constr c
  | RProd (_,Name id,ty,c) ->
      url_string "\\forall "; url_id id; url_string ":";
      uri_of_constr ty; url_string "."; uri_of_constr c
  | RLetIn (_,na,b,c) ->
      url_string "let "; url_of_name na; url_string "\\def ";
      uri_of_constr b; url_string " in "; uri_of_constr c
  | RCast (_,c, CastConv (_,t)) ->
      uri_of_constr c; url_string ":"; uri_of_constr t
  | RRec _ | RIf _ | RLetTuple _ | RCases _ ->
      error "Whelp does not support pattern-matching and (co-)fixpoint"
  | RVar _ | RRef _ | RHole _ | REvar _ | RSort _ | RCast (_,_, CastCoerce) ->
      anomaly "Written w/o parenthesis"
  | RPatVar _ | RDynamic _ -> 
      anomaly "Found constructors not supported in constr") ()

let make_string f x = Buffer.reset b; f x; Buffer.contents b

let send_whelp req s =
  let url = make_whelp_request req s in
  let command = (fst browser_cmd_fmt) ^ url ^ (snd browser_cmd_fmt) in
  let _ = run_command (fun x -> x) print_string command in ()

let whelp_constr req c =
  let c = detype false [whelm_special] [] c in
  send_whelp req (make_string uri_of_constr c)

let whelp_constr_expr req c =
  let (sigma,env)= get_current_context () in
  let _,c = interp_open_constr sigma env c in
  whelp_constr req c

let whelp_locate s =
  send_whelp "locate" s

let whelp_elim ind = 
  send_whelp "elim" (make_string uri_of_global (IndRef ind))

let on_goal f =
  let gls = nth_goal_of_pftreestate 1 (get_pftreestate ()) in
  f (it_mkNamedProd_or_LetIn (pf_concl gls) (pf_hyps gls))

type whelp_request =
  | Locate of string
  | Elim of inductive
  | Constr of string * constr

let whelp = function
  | Locate s -> whelp_locate s
  | Elim ind -> whelp_elim ind
  | Constr (s,c) -> whelp_constr s c

VERNAC ARGUMENT EXTEND whelp_constr_request
| [ "Match" ] -> [ "match" ]
| [ "Instance" ] -> [ "instance" ]
END

VERNAC COMMAND EXTEND Whelp
| [ "Whelp" "Locate" string(s) ] -> [ whelp_locate s ] 
| [ "Whelp" "Locate" preident(s) ] -> [ whelp_locate s ] 
| [ "Whelp" "Elim" global(r) ] -> [ whelp_elim (inductive_of_reference_with_alias r) ] 
| [ "Whelp" whelp_constr_request(req) constr(c) ] -> [ whelp_constr_expr req c]
END

VERNAC COMMAND EXTEND WhelpHint
| [ "Whelp" "Hint" constr(c) ] -> [ whelp_constr_expr "hint" c ] 
| [ "Whelp" "Hint" ] -> [ on_goal (whelp_constr "hint") ] 
END
