
let error_cant_find_case_type loc env expr =
  raise (PretypeError (loc,CCI,context env,CantFindCaseType expr))

let error_ill_formed_branch k env c i actty expty =
  raise (TypeError (k, context env, IllFormedBranch (c,i,actty,expty)))
