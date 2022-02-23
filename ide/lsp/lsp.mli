open Yojson.Basic

type assoct
type lquery
type lsp_query = { query_id: int option; q: lquery }
val lsp_of_response : int option -> t -> t
val unpack_lsp_query : t -> lsp_query

type state_or_exit_t = State of Vernac.State.t | ExitCode of int
type response_state_t = t option * state_or_exit_t
val run_query : Vernac.State.t -> lquery -> response_state_t

val parse_header_len : string Stream.t -> int -> int
val read_lsp_query : string Stream.t -> lsp_query
