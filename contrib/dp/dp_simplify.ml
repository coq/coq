
open Format
open Fol

let is_simplify_ident s =
  let is_simplify_char = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' -> true 
    | _ -> false
  in
  try 
    String.iter (fun c -> if not (is_simplify_char c) then raise Exit) s; true
  with Exit ->
    false

let ident fmt s =
  if is_simplify_ident s then fprintf fmt "%s" s else fprintf fmt "|%s|" s

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let space fmt () = fprintf fmt "@ "
let comma fmt () = fprintf fmt ",@ "

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
      fprintf fmt "%a" ident id
  | App (id, tl) ->
      fprintf fmt "@[(%a@ %a)@]" ident id print_terms tl

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
      fprintf fmt "@[(EQ (%a@ %a) |@@true|)@]" ident id print_terms tl
  | Imp (a, b) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" pp a pp b
  | And (a, b) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" pp a pp b
  | Or (a, b) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" pp a pp b
  | Not a ->
      fprintf fmt "@[(NOT@ %a)@]" pp a
  | Forall (id, _, p) -> 
      fprintf fmt "@[(FORALL (%a)@ %a)@]" ident id pp p
  | Exists (id, _, p) -> 
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" ident id pp p

(**
let rec string_list l = match l with
    [] -> ""
  | [e] -> e
  | e::l' -> e ^ " " ^ (string_list l')
**)

let print_query fmt (decls,concl) =
  let print_decl = function
    | DeclVar (id, [], t) ->
	fprintf fmt "@[;; %s : %s@]@\n"	id t
    | DeclVar (id, l, t) ->
	fprintf fmt "@[;; %s : %a -> %s@]@\n" 
	  id (print_list comma pp_print_string) l t
    | DeclPred (id, []) ->
	fprintf fmt "@[;; %s : BOOLEAN @]@\n" id
    | DeclPred (id, l) -> 
	fprintf fmt "@[;; %s : %a -> BOOLEAN@]@\n" 
	  id (print_list comma pp_print_string) l
    | DeclType id ->
	fprintf fmt "@[;; %s : TYPE@]@\n" id
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
