
open Format
open Fol

let rec print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; sep fmt (); print_list sep print fmt r

let space fmt () = fprintf fmt "@ "

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%s" id
  | Cst n -> 
      fprintf fmt "%d" n
  | Plus _ | Moins _ | Div _ | Mult _ ->
      assert false (*TODO*) (* (+ a b) *)
  | App (id, []) ->
      fprintf fmt "%s" id 
  | App (id, tl) ->
      fprintf fmt "@[(%s@ %a)@]" id print_terms tl
  | Db _ ->
      assert false (*TODO*)

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt p = 
  let pp = print_predicate in 
  match p with
  | True ->
      fprintf fmt "TRUE"
  | False ->
      fprintf fmt "FALSE"
  | Fvar id -> 
      fprintf fmt "%s" id
  | Fatom (Eq (a, b)) ->
      fprintf fmt "@[(EQ %a@ %a)@]" print_term a print_term b
  | Fatom (Le (a, b)) ->
      fprintf fmt "@[(<= %a %a)@]" print_term a print_term b
  | Fatom (Pred (id, tl)) -> 
      fprintf fmt "@[(EQ (%s@ %a) |@@true|)@]" id print_terms tl
  | Fatom _ ->
      assert false (*TODO*)
  | Imp (a, b) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" pp a pp b
  | And (a, b) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" pp a pp b
  | Or (a, b) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" pp a pp b
  | Not a ->
      fprintf fmt "@[(NOT@ %a)@]" pp a
(*
  | Forall (_,id,n,_,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a)@ %a)@]" Ident.print id' pp p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" Ident.print id' pp p'
*)
  | Exists _|Forall _ ->
      assert false (*TODO*)

let print_query fmt (decls,concl) =
  let print_decl = function
    | DeclVar _ | DeclProp _ | DeclType _ -> 
	()
    | Assert (id, f)  -> 
	fprintf fmt "@[(BG_PUSH ;; %s@\n %a)@]@\n" id print_predicate f
  in
  List.iter print_decl decls;
  print_predicate fmt concl

let call q = 
  let f = Filename.temp_file "coq_dp" ".sx" in
  let c = open_out f in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[%a@]@." print_query q;
  close_out c;
  let cmd = 
    sprintf "timeout 10 Simplify %s > out 2>&1 && grep -q -w Valid out" f
  in
  prerr_endline cmd; flush stderr;
  let out = Sys.command cmd in
  if out = 0 then Valid else if out = 1 then Invalid else Timeout
  (* TODO: effacer le fichier f et le fichier out *)


