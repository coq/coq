
let error_cant_find_case_type_loc loc env expr =
  raise (PretypeError (loc,CCI,context env,CantFindCaseType expr))

let error_ill_formed_branch k env c i actty expty =
  raise (TypeError (k, context env, IllFormedBranch (c,i,actty,expty)))

let error_number_branches_loc loc k env c ct expn =
  raise (PretypeError (loc, k, context env, NumberBranches (c,ct,expn)))
