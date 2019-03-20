open Genredexpr

val pr_with_occurrences :
  ('a -> Pp.t) -> (string -> Pp.t) -> 'a Locus.with_occurrences -> Pp.t

val pr_short_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t
val pr_red_flag : ('a -> Pp.t) -> 'a glob_red_flag -> Pp.t

val pr_red_expr :
  ('a -> Pp.t) * ('a -> Pp.t) * ('b -> Pp.t) * ('c -> Pp.t) ->
  (string -> Pp.t) -> ('a,'b,'c) red_expr_gen -> Pp.t
  [@@ocaml.deprecated "Use pr_red_expr_env instead"]

val pr_red_expr_env : Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> 'a -> Pp.t) *
  (Environ.env -> Evd.evar_map -> 'a -> Pp.t) *
  ('b -> Pp.t) *
  (Environ.env -> Evd.evar_map -> 'c -> Pp.t) ->
  (string -> Pp.t) ->
  ('a,'b,'c) red_expr_gen -> Pp.t
