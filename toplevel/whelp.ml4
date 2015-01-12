(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Flags
open Pp
open Errors
open Names
open Term
open Glob_term
open Libnames
open Globnames
open Nametab
open Detyping
open Constrintern
open Dischargedhypsmap
open Pfedit
open Tacmach
open Misctypes

(* Coq interface to the Whelp query engine developed at
   the University of Bologna *)

let whelp_server_name = ref "http://mowgli.cs.unibo.it:58080"
let getter_server_name = ref "http://mowgli.cs.unibo.it:58081"

open Goptions

let _ =
  declare_string_option
    { optsync  = false;
      optdepr  = false;
      optname  = "Whelp server";
      optkey   = ["Whelp";"Server"];
      optread  = (fun () -> !whelp_server_name);
      optwrite = (fun s -> whelp_server_name := s) }

let _ =
  declare_string_option
    { optsync  = false;
      optdepr  = false;
      optname  = "Whelp getter";
      optkey   = ["Whelp";"Getter"];
      optread  = (fun () -> !getter_server_name);
      optwrite = (fun s -> getter_server_name := s) }


let make_whelp_request req c =
  !whelp_server_name ^ "/apply?xmluri=" ^ !getter_server_name ^ "/getempty&param.profile=firewall&profile=firewall&param.keys=d_c%2CC1%2CHC2%2CL&param.embedkeys=d_c%2CTC1%2CHC2%2CL&param.thkeys=T1%2CT2%2CL%2CE&param.prooftreekeys=HAT%2CG%2CHAO%2CL&param.media-type=text%2Fhtml&param.thmedia-type=&prooftreemedia-type=&param.doctype-public=&param.encoding=&param.thencoding=&param.prooftreeencoding=&advanced=no&keys=S%2CT1%2CT2%2CL%2CRT%2CE&param.expression=" ^ c ^ "&param.action=" ^ req

let b = Buffer.create 16

let url_char c =
  if 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' ||
     '0' <= c && c <= '9' || c ='.'
  then Buffer.add_char b c
  else Buffer.add_string b (Printf.sprintf "%%%2X" (Char.code c))

let url_string s = String.iter url_char s

let rec url_list_with_sep sep f = function
  | [] -> ()
  | [a] -> f a
  | a::l -> f a; url_string sep; url_list_with_sep sep f l

let url_id id = url_string (Id.to_string id)

let uri_of_dirpath dir =
  url_string "cic:/"; url_list_with_sep "/" url_id (List.rev dir)

let error_whelp_unknown_reference ref =
  let qid = Nametab.shortest_qualid_of_global Id.Set.empty ref in
  errorlabstrm ""
    (strbrk "Definitions of the current session, like " ++ pr_qualid qid ++
     strbrk ", are not supported in Whelp.")

let uri_of_repr_kn ref (mp,dir,l) =
  match mp with
    | MPfile sl ->
        uri_of_dirpath (Label.to_id l :: DirPath.repr dir @ DirPath.repr sl)
    | _ ->
        error_whelp_unknown_reference ref

let url_paren f l = url_char '('; f l; url_char ')'
let url_bracket f l = url_char '['; f l; url_char ']'

let whelp_of_glob_sort = function
  | GProp -> "Prop"
  | GSet -> "Set"
  | GType _ -> "Type"

let uri_int n = Buffer.add_string b (string_of_int n)

let uri_of_ind_pointer l =
  url_string ".ind#xpointer"; url_paren (url_list_with_sep "/" uri_int) l

let uri_of_global ref =
  match ref with
  | VarRef id -> error ("Unknown Whelp reference: "^(Id.to_string id)^".")
  | ConstRef cst ->
      uri_of_repr_kn ref (repr_con cst); url_string ".con"
  | IndRef (kn,i) ->
      uri_of_repr_kn ref (repr_mind kn); uri_of_ind_pointer [1;i+1]
  | ConstructRef ((kn,i),j) ->
      uri_of_repr_kn ref (repr_mind kn); uri_of_ind_pointer [1;i+1;j]

let whelm_special = Id.of_string "WHELM_ANON_VAR"

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
  | GRef (_,(ConstructRef ((induri,_),_) | IndRef (induri,_)),_) ->
      get_discharged_hyp_names (path_of_global (IndRef(induri,0)))
  | GRef (_,(ConstRef cst as ref),_) ->
      get_discharged_hyp_names (path_of_global ref)
  | _ -> []

let merge vl al =
  let rec aux acc = function
  | ([],l) | (_,([] as l)) -> List.rev acc, l
  | (v::vl,a::al) -> aux ((v,a)::acc) (vl,al)
  in aux [] (vl,al)

let rec uri_of_constr c =
  match c with
  | GVar (_,id) -> url_id id
  | GRef (_,ref,_) ->  uri_of_global ref
  | GHole _ | GEvar _ -> url_string "?"
  | GSort (_,s) -> url_string (whelp_of_glob_sort s)
  | GApp (_,f,args) ->
      let inst,rest = merge (section_parameters f) args in
      uri_of_constr f; url_char ' '; uri_params uri_of_constr inst;
      url_list_with_sep " " uri_of_constr rest
  | GLambda (_,na,k,ty,c) ->
      url_string "\\lambda "; url_of_name na; url_string ":";
      uri_of_constr ty; url_string "."; uri_of_constr c
  | GProd (_,Anonymous,k,ty,c) ->
      uri_of_constr ty; url_string "\\to "; uri_of_constr c
  | GProd (_,Name id,k,ty,c) ->
      url_string "\\forall "; url_id id; url_string ":";
      uri_of_constr ty; url_string "."; uri_of_constr c
  | GLetIn (_,na,b,c) ->
      url_string "let "; url_of_name na; url_string "\\def ";
      uri_of_constr b; url_string " in "; uri_of_constr c
  | GCast (_,c, (CastConv t|CastVM t|CastNative t)) ->
      uri_of_constr c; url_string ":"; uri_of_constr t
  | GRec _ | GIf _ | GLetTuple _ | GCases _ ->
      error "Whelp does not support pattern-matching and (co-)fixpoint."
  | GCast (_,_, CastCoerce) ->
      anomaly (Pp.str "Written w/o parenthesis")
  | GPatVar _ ->
      anomaly (Pp.str "Found constructors not supported in constr")

let make_string f x = Buffer.reset b; f x; Buffer.contents b

let send_whelp req s =
  let url = make_whelp_request req s in
  let command = Util.subst_command_placeholder browser_cmd_fmt url in
  let _ = CUnix.run_command ~hook:print_string command in ()

let whelp_constr env sigma req c =
  let c = detype false [whelm_special] env sigma c in
  send_whelp req (make_string uri_of_constr c)

let whelp_constr_expr req c =
  let (sigma,env)= Lemmas.get_current_context () in
  let _,c = interp_open_constr env sigma c in
  whelp_constr env sigma req c

let whelp_locate s =
  send_whelp "locate" s

let whelp_elim ind =
  send_whelp "elim" (make_string uri_of_global (IndRef ind))

let on_goal f =
  let gls = Proof.V82.subgoals (get_pftreestate ()) in
  let gls = { gls with Evd.it = List.hd gls.Evd.it }  in
  f (pf_env gls) (project gls) (Termops.it_mkNamedProd_or_LetIn (pf_concl gls) (pf_hyps gls))

type whelp_request =
  | Locate of string
  | Elim of inductive
  | Constr of string * constr

let whelp = function
  | Locate s -> whelp_locate s
  | Elim ind -> whelp_elim ind
  | Constr (s,c) -> whelp_constr (Global.env()) (Evd.empty) s c

VERNAC ARGUMENT EXTEND whelp_constr_request
| [ "Match" ] -> [ "match" ]
| [ "Instance" ] -> [ "instance" ]
END

VERNAC COMMAND EXTEND Whelp CLASSIFIED AS QUERY
| [ "Whelp" "Locate" string(s) ] -> [ whelp_locate s ]
| [ "Whelp" "Locate" preident(s) ] -> [ whelp_locate s ]
| [ "Whelp" "Elim" global(r) ] -> [ whelp_elim (Smartlocate.global_inductive_with_alias r) ]
| [ "Whelp" whelp_constr_request(req) constr(c) ] -> [ whelp_constr_expr req c]
END

VERNAC COMMAND EXTEND WhelpHint CLASSIFIED AS QUERY
| [ "Whelp" "Hint" constr(c) ] -> [ whelp_constr_expr "hint" c ]
| [ "Whelp" "Hint" ] => [ Vernacexpr.VtProofStep false, Vernacexpr.VtLater ] ->
  [ on_goal (fun env sigma -> whelp_constr env sigma "hint") ]
END
