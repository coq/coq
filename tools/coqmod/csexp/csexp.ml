module type Sexp = sig
  type t =
    | Atom of string
    | List of t list
end

module type Monad = sig
  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module type S = sig
  type sexp

  val parse_string : string -> (sexp, int * string) result

  val parse_string_many : string -> (sexp list, int * string) result

  val input : in_channel -> (sexp, string) result

  val input_opt : in_channel -> (sexp option, string) result

  val input_many : in_channel -> (sexp list, string) result

  val serialised_length : sexp -> int

  val to_string : sexp -> string

  val to_buffer : Buffer.t -> sexp -> unit

  val to_channel : out_channel -> sexp -> unit

  module Parser : sig
    exception Parse_error of string

    val premature_end_of_input : string

    module Lexer : sig
      type t

      val create : unit -> t

      type _ token =
        | Await : [> `other ] token
        | Lparen : [> `other ] token
        | Rparen : [> `other ] token
        | Atom : int -> [> `atom ] token

      val feed : t -> char -> [ `other | `atom ] token

      val feed_eoi : t -> unit
    end

    module Stack : sig
      type t =
        | Empty
        | Open of t
        | Sexp of sexp * t

      val to_list : t -> sexp list

      val open_paren : t -> t

      val close_paren : t -> t

      val add_atom : string -> t -> t

      val add_token : [ `other ] Lexer.token -> t -> t
    end
  end

  module type Input = sig
    type t

    module Monad : sig
      type 'a t

      val return : 'a -> 'a t

      val bind : 'a t -> ('a -> 'b t) -> 'b t
    end

    val read_string : t -> int -> (string, string) result Monad.t

    val read_char : t -> (char, string) result Monad.t
  end
  [@@deprecated "Use Parser module instead"]

  [@@@warning "-3"]

  module Make_parser (Input : Input) : sig
    val parse : Input.t -> (sexp, string) result Input.Monad.t

    val parse_many : Input.t -> (sexp list, string) result Input.Monad.t
  end
  [@@deprecated "Use Parser module instead"]
end

module Make (Sexp : Sexp) = struct
  open Sexp

  module Parser = struct
    exception Parse_error of string

    let parse_error msg = raise (Parse_error msg)

    let parse_errorf f = Format.ksprintf parse_error f

    let premature_end_of_input = "premature end of input"

    module Lexer = struct
      type state =
        | Init
        | Parsing_length

      type t =
        { mutable state : state
        ; mutable n : int
        }

      let create () = { state = Init; n = 0 }

      let int_of_digit c = Char.code c - Char.code '0'

      type _ token =
        | Await : [> `other ] token
        | Lparen : [> `other ] token
        | Rparen : [> `other ] token
        | Atom : int -> [> `atom ] token

      let feed t c =
        match (t.state, c) with
        | Init, '(' -> Lparen
        | Init, ')' -> Rparen
        | Init, '0' .. '9' ->
          t.state <- Parsing_length;
          t.n <- int_of_digit c;
          Await
        | Init, _ ->
          parse_errorf "invalid character %C, expected '(', ')' or '0'..'9'" c
        | Parsing_length, '0' .. '9' ->
          let len = (t.n * 10) + int_of_digit c in
          if len > Sys.max_string_length then
            parse_error "atom too big to represent"
          else (
            t.n <- len;
            Await
          )
        | Parsing_length, ':' ->
          t.state <- Init;
          Atom t.n
        | Parsing_length, _ ->
          parse_errorf
            "invalid character %C while parsing atom length, expected '0'..'9' \
             or ':'"
            c

      let feed_eoi t =
        match t.state with
        | Init -> ()
        | Parsing_length -> parse_error premature_end_of_input
    end

    module L = Lexer

    module Stack = struct
      type t =
        | Empty
        | Open of t
        | Sexp of Sexp.t * t

      let open_paren stack = Open stack

      let close_paren =
        let rec loop acc = function
          | Empty ->
            parse_error "right parenthesis without matching left parenthesis"
          | Sexp (sexp, t) -> loop (sexp :: acc) t
          | Open t -> Sexp (List acc, t)
        in
        fun t -> loop [] t

      let to_list =
        let rec loop acc = function
          | Empty -> acc
          | Sexp (sexp, t) -> loop (sexp :: acc) t
          | Open _ -> parse_error premature_end_of_input
        in
        fun t -> loop [] t

      let add_atom s stack = Sexp (Atom s, stack)

      let add_token (x : [ `other ] Lexer.token) stack =
        match x with
        | L.Await -> stack
        | L.Lparen -> open_paren stack
        | L.Rparen -> close_paren stack
    end
  end

  open Parser

  let feed_eoi_single lexer stack =
    match
      Lexer.feed_eoi lexer;
      Stack.to_list stack
    with
    | exception Parse_error msg -> Error msg
    | [ x ] -> Ok x
    | [] -> Error premature_end_of_input
    | _ :: _ :: _ -> assert false

  let feed_eoi_many lexer stack =
    match
      Lexer.feed_eoi lexer;
      Stack.to_list stack
    with
    | exception Parse_error msg -> Error msg
    | l -> Ok l

  let one_token s pos len lexer stack k =
    match Lexer.feed lexer (String.unsafe_get s pos) with
    | exception Parse_error msg -> Error (pos, msg)
    | L.Atom atom_len -> (
      match String.sub s (pos + 1) atom_len with
      | exception _ -> Error (len, premature_end_of_input)
      | atom ->
        let pos = pos + 1 + atom_len in
        k s pos len lexer (Stack.add_atom atom stack) )
    | (L.Await | L.Lparen | L.Rparen) as x -> (
      match Stack.add_token x stack with
      | exception Parse_error msg -> Error (pos, msg)
      | stack -> k s (pos + 1) len lexer stack )
    [@@inlined always]

  let parse_string =
    let rec loop s pos len lexer stack =
      if pos = len then
        match feed_eoi_single lexer stack with
        | Error msg -> Error (pos, msg)
        | Ok _ as ok -> ok
      else
        one_token s pos len lexer stack cont
    and cont s pos len lexer stack =
      match stack with
      | Stack.Sexp (sexp, Empty) ->
        if pos = len then
          Ok sexp
        else
          Error (pos, "data after canonical S-expression")
      | stack -> loop s pos len lexer stack
    in
    fun s -> loop s 0 (String.length s) (Lexer.create ()) Empty

  let parse_string_many =
    let rec loop s pos len lexer stack =
      if pos = len then
        match feed_eoi_many lexer stack with
        | Error msg -> Error (pos, msg)
        | Ok _ as ok -> ok
      else
        one_token s pos len lexer stack loop
    in
    fun s -> loop s 0 (String.length s) (Lexer.create ()) Empty

  let one_token ic c lexer stack =
    match Lexer.feed lexer c with
    | L.Atom n -> (
      match really_input_string ic n with
      | exception End_of_file -> raise (Parse_error premature_end_of_input)
      | s -> Stack.add_atom s stack )
    | (L.Await | L.Lparen | L.Rparen) as x -> Stack.add_token x stack

  let input_opt =
    let rec loop ic lexer stack =
      let c = input_char ic in
      match one_token ic c lexer stack with
      | Sexp (sexp, Empty) -> Ok (Some sexp)
      | stack -> loop ic lexer stack
    in
    fun ic ->
      let lexer = Lexer.create () in
      match input_char ic with
      | exception End_of_file -> Ok None
      | c -> (
        try
          match Lexer.feed lexer c with
          | L.Atom _ -> assert false
          | (L.Await | L.Lparen | L.Rparen) as x ->
            loop ic lexer (Stack.add_token x Empty)
        with
        | Parse_error msg -> Error msg
        | End_of_file -> Error premature_end_of_input )

  let input ic =
    match input_opt ic with
    | Ok None -> Error premature_end_of_input
    | Ok (Some x) -> Ok x
    | Error msg -> Error msg

  let input_many =
    let rec loop ic lexer stack =
      match input_char ic with
      | exception End_of_file ->
        Lexer.feed_eoi lexer;
        Ok (Stack.to_list stack)
      | c -> loop ic lexer (one_token ic c lexer stack)
    in
    fun ic ->
      try loop ic (Lexer.create ()) Empty with Parse_error msg -> Error msg

  let serialised_length =
    let rec loop acc t =
      match t with
      | Atom s ->
        let len = String.length s in
        let x = ref len in
        let len_len = ref 1 in
        while !x > 9 do
          x := !x / 10;
          incr len_len
        done;
        acc + !len_len + 1 + len
      | List l -> List.fold_left loop acc l
    in
    fun t -> loop 0 t

  let to_buffer buf sexp =
    let rec loop = function
      | Atom str ->
        Buffer.add_string buf (string_of_int (String.length str));
        Buffer.add_string buf ":";
        Buffer.add_string buf str
      | List e ->
        Buffer.add_char buf '(';
        List.iter loop e;
        Buffer.add_char buf ')'
    in
    loop sexp

  let to_string sexp =
    let buf = Buffer.create (serialised_length sexp) in
    to_buffer buf sexp;
    Buffer.contents buf

  let to_channel oc sexp =
    let rec loop = function
      | Atom str ->
        output_string oc (string_of_int (String.length str));
        output_char oc ':';
        output_string oc str
      | List l ->
        output_char oc '(';
        List.iter loop l;
        output_char oc ')'
    in
    loop sexp

  module type Input = sig
    type t

    module Monad : Monad

    val read_string : t -> int -> (string, string) result Monad.t

    val read_char : t -> (char, string) result Monad.t
  end

  module Make_parser (Input : Input) = struct
    open Input.Monad

    let ( >>= ) = bind

    let ( >>=* ) m f =
      m >>= function
      | Error _ as err -> return err
      | Ok x -> f x

    let one_token input c lexer stack =
      match Lexer.feed lexer c with
      | exception Parse_error msg -> return (Error msg)
      | L.Atom n ->
        Input.read_string input n >>=* fun s ->
        return (Ok (Stack.add_atom s stack))
      | (L.Await | L.Lparen | L.Rparen) as x ->
        return
          ( match Stack.add_token x stack with
          | exception Parse_error msg -> Error msg
          | stack -> Ok stack )

    let parse =
      let rec loop input lexer stack =
        Input.read_char input >>= function
        | Error _ -> return (feed_eoi_single lexer stack)
        | Ok c -> (
          one_token input c lexer stack >>=* function
          | Sexp (sexp, Empty) -> return (Ok sexp)
          | stack -> loop input lexer stack )
      in
      fun input -> loop input (Lexer.create ()) Empty

    let parse_many =
      let rec loop input lexer stack =
        Input.read_char input >>= function
        | Error _ -> return (feed_eoi_many lexer stack)
        | Ok c ->
          one_token input c lexer stack >>=* fun stack -> loop input lexer stack
      in
      fun input -> loop input (Lexer.create ()) Empty
  end
end

module T = struct
  type t =
    | Atom of string
    | List of t list
end

include T
include Make (T)
