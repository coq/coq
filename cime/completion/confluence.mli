

module type Confluence = 
sig
  type symbol
  type signature 
  type variables
  type simple_rule 
  val is_confluent : signature -> variables -> simple_rule list -> bool 
  val print_all_critical_pairs : 
    signature -> variables -> simple_rule list -> unit
end
  
module Make (R : Abstract_rewriting.AbstractRewriting) : 
  (Confluence 
   with type symbol = R.symbol
   and type signature = R.signature
   and type variables = R.variables
   and type simple_rule = R.rule)

module StandardConfluence :  
  (Confluence 
   with type symbol = User_signatures.symbol_id
   and type signature = User_signatures.symbol_id Signatures.signature
   and type variables = Variables.user_variables
   and type simple_rule = User_signatures.symbol_id Rewrite_rules.rewrite_rule)

module ACConfluence : 
  (Confluence
   with type symbol = User_signatures.symbol_id
   and type signature = User_signatures.symbol_id Signatures.signature
   and type variables = Variables.user_variables
   and type simple_rule = User_signatures.symbol_id Rewrite_rules.rewrite_rule)


	
