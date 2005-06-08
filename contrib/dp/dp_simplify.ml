
open Format
open Fol

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let space fmt () = fprintf fmt "@ "

let rec print_term fmt = function
  | Cst n -> 
      fprintf fmt "%d" n
  | Plus (a, b) ->
      fprintf fmt "@[(+@ %a@ %a)@]" print_term a print_term b
  | Moins (a, b) ->
      fprintf fmt "@[(-@ %a@ %a)@]" print_term a print_term b
  | Mult (a, b) ->
      fprintf fmt "@[(*@ %a@ %a)@]" print_term a print_term b
  | Div (a, b) ->
      fprintf fmt "@[(/@ %a@ %a)@]" print_term a print_term b
  | App (id, []) ->
      fprintf fmt "%s" id 
  | App (id, tl) ->
      fprintf fmt "@[(%s@ %a)@]" id print_terms tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt p = 
  let pp = print_predicate in 
  match p with
  | True ->
      fprintf fmt "TRUE"
  | False ->
      fprintf fmt "FALSE"
  | Fatom (Eq (a, b)) ->
      fprintf fmt "@[(EQ %a@ %a)@]" print_term a print_term b
  | Fatom (Le (a, b)) ->
      fprintf fmt "@[(<= %a@ %a)@]" print_term a print_term b
  | Fatom (Lt (a, b))->
      fprintf fmt "@[(< %a@ %a)@]" print_term a print_term b
  | Fatom (Ge (a, b)) ->
      fprintf fmt "@[(>= %a@ %a)@]" print_term a print_term b
  | Fatom (Gt (a, b)) ->
      fprintf fmt "@[(> %a@ %a)@]" print_term a print_term b
  | Fatom (Pred (id, tl)) -> 
      fprintf fmt "@[(EQ (%s@ %a) |@@true|)@]" id print_terms tl
  | Imp (a, b) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" pp a pp b
  | And (a, b) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" pp a pp b
  | Or (a, b) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" pp a pp b
  | Not a ->
      fprintf fmt "@[(NOT@ %a)@]" pp a
  | Forall (id, _, p) -> 
      fprintf fmt "@[(FORALL (%s)@ %a)@]" id pp p
(*
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" Ident.print id' pp p'
*)
  | Exists _ ->
      assert false (*TODO*)

let rec string_of_type_list  = function
  | [] -> ""
  | e :: l' -> e ^ " -> " ^ (string_of_type_list l')

let print_query fmt (decls,concl) =
  let print_decl = function
    | DeclVar (id, [], t) ->
	fprintf fmt "@[;; %s: %s@]@\n" id t
    | DeclVar (id, l, t) ->
	fprintf fmt "@[;; %s: %s%s@]@\n"
	  id (string_of_type_list l) t
    | DeclPred (id, l) -> 
	fprintf fmt "@[;; %s: %sBOOLEAN@]@\n"
	  id (string_of_type_list l)
    | DeclType id ->
	fprintf fmt "@[;; %s: TYPE@]@\n" id
    | Assert (id, f)  -> 
	fprintf fmt "@[(BG_PUSH ;; %s@\n %a)@]@\n" id print_predicate f
  in
  List.iter print_decl decls;
  fprintf fmt "%a@." print_predicate concl

let call q = 
  let f = Filename.temp_file "coq_dp" ".sx" in
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[%a@]@." print_query q;
  close_out c;
  ignore (Sys.command (sprintf "cat %s" f));
  let cmd = 
    sprintf "timeout 10 Simplify %s > out 2>&1 && grep -q -w Valid out" f
  in
  prerr_endline cmd; flush stderr;
  let out = Sys.command cmd in
  if out = 0 then Valid else if out = 1 then Invalid else Timeout
  (* TODO: effacer le fichier f et le fichier out *)


