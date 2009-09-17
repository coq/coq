
{

  open Lexing
  open Pp
  open Util
  open Names
  open Tacmach
  open Dp_why
  open Tactics
  open Tacticals

  let debug = ref false
  let set_debug b = debug := b

  let buf = Buffer.create 1024

  let string_of_global env ref =
    Libnames.string_of_qualid (Nametab.shortest_qualid_of_global env ref)

  let axioms = ref []

  (* we cannot interpret the terms as we read them (since some lemmas
     may need other lemmas to be already interpreted) *)
  type lemma = { l_id : string; l_type : string; l_proof : string }
  type zenon_proof = lemma list * string

}

let ident = ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']+
let space = [' ' '\t' '\r']

rule start = parse
| "(* BEGIN-PROOF *)" "\n" { scan lexbuf }
| _ { start lexbuf }
| eof { anomaly "malformed Zenon proof term" }

(* here we read the lemmas and the main proof term;
   meanwhile we maintain the set of axioms that were used *)

and scan = parse
| "Let" space (ident as id) space* ":"
  { let t = read_coq_term lexbuf in
    let p = read_lemma_proof lexbuf in
    let l,pr = scan lexbuf in
    { l_id = id; l_type = t; l_proof = p } :: l, pr }
| "Definition theorem:"
  { let t = read_main_proof lexbuf in [], t }
| _ | eof
  { anomaly "malformed Zenon proof term" }

and read_coq_term = parse
| "." "\n"
  { let s = Buffer.contents buf in Buffer.clear buf; s }
| "coq__" (ident as id) (* a Why keyword renamed *)
  { Buffer.add_string buf id; read_coq_term lexbuf }
| ("dp_axiom__" ['0'-'9']+) as id
  { axioms := id :: !axioms; Buffer.add_string buf id; read_coq_term lexbuf }
| _ as c
  { Buffer.add_char buf c; read_coq_term lexbuf }
| eof
  { anomaly "malformed Zenon proof term" }

and read_lemma_proof = parse
| "Proof" space
  { read_coq_term lexbuf }
| _ | eof
  { anomaly "malformed Zenon proof term" }

(* skip the main proof statement and then read its term *)
and read_main_proof = parse
| ":=" "\n"
  { read_coq_term lexbuf }
| _
  { read_main_proof lexbuf }
| eof
  { anomaly "malformed Zenon proof term" }


{

  let read_zenon_proof f =
    Buffer.clear buf;
    let c = open_in f in
    let lb = from_channel c in
    let p = start lb in
    close_in c;
    if not !debug then begin try Sys.remove f with _ -> () end;
    p

  let constr_of_string gl s =
    let parse_constr = Pcoq.parse_string Pcoq.Constr.constr in
    Constrintern.interp_constr (project gl) (pf_env gl) (parse_constr s)

  (* we are lazy here: we build strings containing Coq terms using a *)
  (* pretty-printer Fol -> Coq *)
  module Coq = struct
    open Format
    open Fol

    let rec print_list sep print fmt = function
      | [] -> ()
      | [x] -> print fmt x
      | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

    let space fmt () = fprintf fmt "@ "
    let comma fmt () = fprintf fmt ",@ "

    let rec print_typ fmt = function
      | Tvar x -> fprintf fmt "%s" x
      | Tid ("int", []) -> fprintf fmt "Z"
      | Tid (x, []) -> fprintf fmt "%s" x
      | Tid (x, [t]) -> fprintf fmt "(%s %a)" x print_typ t
      | Tid (x,tl) ->
	  fprintf fmt "(%s %a)" x (print_list comma print_typ) tl

    let rec print_term fmt = function
      | Cst n ->
	  fprintf fmt "%s" (Big_int.string_of_big_int n)
      | RCst s ->
          fprintf fmt "%s" (Big_int.string_of_big_int s)
      | Power2 n ->
          fprintf fmt "@[(powerRZ 2 %s)@]" (Big_int.string_of_big_int n)

          (* TODO: bug, it might be operations on reals *)
      | Plus (a, b) ->
	  fprintf fmt "@[(Zplus %a %a)@]" print_term a print_term b
      | Moins (a, b) ->
	  fprintf fmt "@[(Zminus %a %a)@]" print_term a print_term b
      | Mult (a, b) ->
	  fprintf fmt "@[(Zmult %a %a)@]" print_term a print_term b
      | Div (a, b) ->
	  fprintf fmt "@[(Zdiv %a %a)@]" print_term a print_term b
      | Opp (a) ->
	  fprintf fmt "@[(Zopp %a)@]" print_term a
      | App (id, []) ->
	  fprintf fmt "%s" id
      | App (id, tl) ->
	  fprintf fmt "@[(%s %a)@]" id print_terms tl

    and print_terms fmt tl =
      print_list space print_term fmt tl

    (* builds the text for "forall vars, f vars = t" *)
    let fun_def_axiom f vars t =
      let binder fmt (x,t) = fprintf fmt "(%s: %a)" x print_typ t in
      fprintf str_formatter
	"@[(forall %a, %s %a = %a)@]@."
	(print_list space binder) vars f
	(print_list space (fun fmt (x,_) -> pp_print_string fmt x)) vars
	print_term t;
      flush_str_formatter ()

  end

  let prove_axiom id = match Dp_why.find_proof id with
    | Immediate t ->
	exact_check t
    | Fun_def (f, vars, ty, t) ->
	tclTHENS
	  (fun gl ->
	     let s = Coq.fun_def_axiom f vars t in
	     if !debug then Format.eprintf "axiom fun def = %s@." s;
	     let c = constr_of_string gl s in
	     assert_tac (Name (id_of_string id)) c gl)
	  [tclTHEN intros reflexivity; tclIDTAC]

  let exact_string s gl =
    let c = constr_of_string gl s in
    exact_check c gl

  let interp_zenon_proof (ll,p) =
    let interp_lemma l gl =
      let ty = constr_of_string gl l.l_type in
      tclTHENS
	(assert_tac (Name (id_of_string l.l_id)) ty)
	[exact_string l.l_proof; tclIDTAC]
	gl
    in
    tclTHEN (tclMAP interp_lemma ll) (exact_string p)

  let proof_from_file f =
    axioms := [];
    msgnl (str "proof_from_file " ++ str f);
    let zp = read_zenon_proof f in
    msgnl (str "proof term is " ++ str (snd zp));
    tclTHEN (tclMAP prove_axiom !axioms) (interp_zenon_proof zp)

}
