open Format

let do_parse s = 
    try
    let b = Lexing.from_string s
    in
      Parameterized_signatures_parser.cword_eof 
	Parameterized_signatures_lexer.token b
  with
      Parsing.Parse_error -> 
	raise (Parameterized_signatures_syntax.Syntax_error "remember to enclose expr. and constr. with {}")
    | Failure "lexing: empty token" -> 
	raise (Parameterized_signatures_syntax.Syntax_error 
		  "invalid character")
    | Poly_syntax.Syntax_error s -> 
	raise (Parameterized_signatures_syntax.Syntax_error s)
    | Parameterized_signatures_syntax.Syntax_error s-> 
	raise (Parameterized_signatures_syntax.Syntax_error s)

open Parameterized_words
  
let from_string (s:Parameterized_signatures.parameterized_signature) c = 
  let w = do_parse c in
  from_abstract_word s w

let rec print_factor f = match f with 
    {base = b; operator = No} -> 
      List.iter 
	(function {a=a;index=l} -> 
	   (printf "%s" a ; 
	    List.iter (function e -> printf "{";
			 Linear_constraints.print_expr e;
			 printf "}"
		      )
	      l;
	    printf "@ "))	
	b
  | {base = b; operator = Power(p)} -> 
      printf "( ";
      print_factor {base = b; operator = No};
      printf ")^{ ";
      Linear_constraints.print_expr p; 
      printf "}@ "	  
	
  | {base = b; operator = Fp(_)} -> printf "<FP>@ "
;;

let print_letters = List.iter print_factor 
;;

let print_env l =
  printf "@[[";
  List.iter 
    (fun v -> 
       Linear_constraints.print_expr (Linear_constraints.var v);
       printf "@ ";
    ) 
    l;
  printf "]@]@ "
;;

let pretty_print c = 
  printf "@[";
  print_env c.env;
  print_letters c.letters;
  printf "|@ { ";
  Linear_constraints.print c.constr;
  printf "}@]"

let interactive_ordering x y = 
  printf "@[Compare :@ ";
  pretty_print x;
  printf "@.AND :@ ";
  pretty_print y;
  printf "@.(<,>,=)@]@.";
  match input_char stdin with
    | '<' -> Orderings_generalities.Less_than
    | '>' -> Orderings_generalities.Greater_than
    | '=' -> Orderings_generalities.Equivalent
    | _ ->  Orderings_generalities.Uncomparable
