(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(** System utilities *)

(** {6 Files and load paths} *)

(** Load path entries remember the original root
    given by the user. For efficiency, we keep the full path (field
    [directory]), the root path and the path relative to the root. *)

type physical_path = string
type load_path = physical_path list

val canonical_path_name : string -> string

val exclude_search_in_dirname : string -> unit

val all_subdirs : unix_path:string -> (physical_path * string list) list
val is_in_path : load_path -> string -> bool
val is_in_system_path : string -> bool
val where_in_path : ?warn:bool -> load_path -> string -> physical_path * string

val physical_path_of_string : string -> physical_path
val string_of_physical_path : physical_path -> string

val make_suffix : string -> string -> string
val file_readable_p : string -> bool

val expand_path_macros : string -> string
val getenv_else : string -> string -> string
val home : string

val exists_dir : string -> bool

val find_file_in_path :
  ?warn:bool -> load_path -> string -> physical_path * string

(** {6 I/O functions } *)
(** Generic input and output functions, parameterized by a magic number
  and a suffix. The intern functions raise the exception [Bad_magic_number]
  when the check fails, with the full file name. *)

val marshal_out : out_channel -> 'a -> unit
val marshal_in : in_channel -> 'a

exception Bad_magic_number of string

val raw_extern_intern : int -> string ->
  (string -> string * out_channel) * (string -> in_channel)

val extern_intern : ?warn:bool -> int -> string ->
  (string -> 'a -> unit) * (load_path -> string -> 'a)

(** {6 Sending/receiving once with external executable } *)

val connect : (out_channel -> unit) -> (in_channel -> 'a) -> string -> 'a

(** {6 Executing commands } *)
(** [run_command converter f com] launches command [com], and returns
    the contents of stdout and stderr that have been processed with
    [converter]; the processed contents of stdout and stderr is also
    passed to [f] *)

val run_command : (string -> string) -> (string -> unit) -> string ->
  Unix.process_status * string

val search_exe_in_path : string -> string option

(** {6 Time stamps.} *)

type time

val process_time : unit -> float * float
val get_time : unit -> time
val time_difference : time -> time -> float (** in seconds *)
val fmt_time_difference : time -> time -> Pp.std_ppcmds
