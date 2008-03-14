
(* Pretty-print PFOL (see fol.mli) in Why syntax *)

open Format
open Fol

type proof = 
  | Immediate of Term.constr
  | Fun_def of string * (string * typ) list * typ * term

let proofs = Hashtbl.create 97
let proof_name = 
  let r = ref 0 in fun () -> incr r; "dp_axiom__" ^ string_of_int !r

let add_proof pr = let n = proof_name () in Hashtbl.add proofs n pr; n

let find_proof = Hashtbl.find proofs

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let space fmt () = fprintf fmt "@ "
let comma fmt () = fprintf fmt ",@ "

let is_why_keyword = 
  let h = Hashtbl.create 17 in
  List.iter 
    (fun s -> Hashtbl.add h s ())
    ["absurd"; "and"; "array"; "as"; "assert"; "axiom"; "begin";
     "bool"; "do"; "done"; "else"; "end"; "exception"; "exists";
     "external"; "false"; "for"; "forall"; "fun"; "function"; "goal";
     "if"; "in"; "int"; "invariant"; "label"; "let"; "logic"; "not";
     "of"; "or"; "parameter"; "predicate"; "prop"; "raise"; "raises";
     "reads"; "real"; "rec"; "ref"; "returns"; "then"; "true"; "try";
     "type"; "unit"; "variant"; "void"; "while"; "with"; "writes" ]; 
  Hashtbl.mem h

let ident fmt s =
  if is_why_keyword s then fprintf fmt "coq__%s" s else fprintf fmt "%s" s

let rec print_typ fmt = function
  | Tvar x -> fprintf fmt "'%a" ident x
  | Tid ("int", []) -> fprintf fmt "int"
  | Tid (x, []) -> fprintf fmt "%a" ident x
  | Tid (x, [t]) -> fprintf fmt "%a %a" print_typ t ident x
  | Tid (x,tl) -> fprintf fmt "(%a) %a" (print_list comma print_typ) tl ident x

let rec print_term fmt = function
  | Cst n -> 
      fprintf fmt "%d" n
  | Plus (a, b) ->
      fprintf fmt "@[(%a +@ %a)@]" print_term a print_term b
  | Moins (a, b) ->
      fprintf fmt "@[(%a -@ %a)@]" print_term a print_term b
  | Mult (a, b) ->
      fprintf fmt "@[(%a *@ %a)@]" print_term a print_term b
  | Div (a, b) ->
      fprintf fmt "@[(%a /@ %a)@]" print_term a print_term b
  | App (id, []) ->
      fprintf fmt "%a" ident id
  | App (id, tl) ->
      fprintf fmt "@[%a(%a)@]" ident id print_terms tl

and print_terms fmt tl = 
  print_list comma print_term fmt tl

let rec print_predicate fmt p = 
  let pp = print_predicate in 
  match p with
  | True ->
      fprintf fmt "true"
  | False ->
      fprintf fmt "false"
  | Fatom (Eq (a, b)) ->
      fprintf fmt "@[(%a =@ %a)@]" print_term a print_term b
  | Fatom (Le (a, b)) ->
      fprintf fmt "@[(%a <=@ %a)@]" print_term a print_term b
  | Fatom (Lt (a, b))->
      fprintf fmt "@[(%a <@ %a)@]" print_term a print_term b
  | Fatom (Ge (a, b)) ->
      fprintf fmt "@[(%a >=@ %a)@]" print_term a print_term b
  | Fatom (Gt (a, b)) ->
      fprintf fmt "@[(%a >@ %a)@]" print_term a print_term b
  | Fatom (Pred (id, [])) -> 
      fprintf fmt "%a" ident id
  | Fatom (Pred (id, tl)) -> 
      fprintf fmt "@[%a(%a)@]" ident id print_terms tl
  | Imp (a, b) ->
      fprintf fmt "@[(%a ->@ %a)@]" pp a pp b
  | Iff (a, b) ->
      fprintf fmt "@[(%a <->@ %a)@]" pp a pp b
  | And (a, b) ->
      fprintf fmt "@[(%a and@ %a)@]" pp a pp b
  | Or (a, b) ->
      fprintf fmt "@[(%a or@ %a)@]" pp a pp b
  | Not a ->
      fprintf fmt "@[(not@ %a)@]" pp a
  | Forall (id, t, p) -> 
      fprintf fmt "@[(forall %a:%a.@ %a)@]" ident id print_typ t pp p
  | Exists (id, t, p) -> 
      fprintf fmt "@[(exists %a:%a.@ %a)@]" ident id print_typ t pp p

let print_query fmt (decls,concl) =
  let print_dtype = function
    | DeclType (id, 0) ->
	fprintf fmt "@[type %a@]@\n@\n" ident id
    | DeclType (id, 1) ->
	fprintf fmt "@[type 'a %a@]@\n@\n" ident id
    | DeclType (id, n) ->
	fprintf fmt "@[type (";
	for i = 1 to n do 
	  fprintf fmt "'a%d" i; if i < n then fprintf fmt ", "
	done;
	fprintf fmt ") %a@]@\n@\n" ident id
    | DeclFun _ | DeclPred _ | Axiom _ ->
	()
  in
  let print_dvar_dpred = function
    | DeclFun (id, _, [], t) ->
	fprintf fmt "@[logic %a : -> %a@]@\n@\n" ident id print_typ t
    | DeclFun (id, _, l, t) ->
	fprintf fmt "@[logic %a : %a -> %a@]@\n@\n" 
	  ident id (print_list comma print_typ) l print_typ t
    | DeclPred (id, _, []) ->
	fprintf fmt "@[logic %a : -> prop @]@\n@\n" ident id
    | DeclPred (id, _, l) -> 
	fprintf fmt "@[logic %a : %a -> prop@]@\n@\n" 
	  ident id (print_list comma print_typ) l
    | DeclType _ | Axiom _ ->
	()
  in
  let print_assert = function
    | Axiom (id, f)  -> 
	fprintf fmt "@[<hov 2>axiom %a:@ %a@]@\n@\n" ident id print_predicate f
    | DeclType _ | DeclFun _ | DeclPred _ ->
	()
  in
  List.iter print_dtype decls;
  List.iter print_dvar_dpred decls;
  List.iter print_assert decls;
  fprintf fmt "@[<hov 2>goal coq___goal: %a@]" print_predicate concl

let output_file f q =
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[%a@]@." print_query q;
  close_out c


