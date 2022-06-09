(** Canonical S-expressions *)

(** This module provides minimal support for reading and writing S-expressions
    in canonical form.

    https://en.wikipedia.org/wiki/Canonical_S-expressions

    Note that because the canonical representation of S-expressions is so
    simple, this module doesn't go out of his way to provide a fully generic
    parser and printer and instead just provides a few simple functions. If you
    are using fancy input sources, simply copy the parser and adapt it. The
    format is so simple that it's pretty difficult to get it wrong by accident.

    To avoid a dependency on a particular S-expression library, the only module
    of this library is parameterised by the type of S-expressions.

    {[
      let rec print = function
        | Atom str -> Printf.printf "%d:%s" (String.length s)
        | List l -> List.iter print l
    ]} *)

module type Sexp = sig
  type t =
    | Atom of string
    | List of t list
end

module type S = sig
  (** {2 Parsing} *)
  type sexp

  (** [parse_string s] parses a single S-expression encoded in canonical form in
      [s]. It is an error for [s] to contain a S-expression followed by more
      data. In case of error, the offset of the error as well as an error
      message is returned. *)
  val parse_string : string -> (sexp, int * string) result

  (** [parse_string s] parses a sequence of S-expressions encoded in canonical
      form in [s] *)
  val parse_string_many : string -> (sexp list, int * string) result

  (** Read exactly one canonical S-expressions from the given channel. Note that
      this function never raises [End_of_file]. Instead, it returns [Error]. *)
  val input : in_channel -> (sexp, string) result

  (** Same as [input] but returns [Ok None] if the end of file has already been
      reached. If some more characters are available but the end of file is
      reached before reading a complete S-expression, this function returns
      [Error]. *)
  val input_opt : in_channel -> (sexp option, string) result

  (** Read many S-expressions until the end of input is reached. *)
  val input_many : in_channel -> (sexp list, string) result

  (** {2 Serialising} *)

  (** The length of the serialised representation of a S-expression *)
  val serialised_length : sexp -> int

  (** [to_string sexp] converts S-expression [sexp] to a string in canonical
      form. *)
  val to_string : sexp -> string

  (** [to_buffer buf sexp] outputs the S-expression [sexp] converted to its
      canonical form to buffer [buf]. *)
  val to_buffer : Buffer.t -> sexp -> unit

  (** [output oc sexp] outputs the S-expression [sexp] converted to its
      canonical form to channel [oc]. *)
  val to_channel : out_channel -> sexp -> unit

  (** {3 Low level parser}

      For efficiently parsing from sources other than strings or input channel.
      For instance in Lwt or Async programs. *)

  module Parser : sig
    (** The [Parser] module offers an API that is a balance between sharing the
        common logic of parsing canonical S-expressions while allowing to write
        parsers that are as efficient as possible, both in terms of speed and
        allocations. A carefully written parser using this API will be:

        - fast
        - perform minimal allocations
        - perform zero [caml_modify] (a slow function of the OCaml runtime that
          is emitted when mutating a constructed value)

        {2 Lexers}

        To parse using this API, you must first create a lexer via
        {!Lexer.create}. The lexer is responsible for scanning the input and
        forming tokens. The user must feed characters read from the input one by
        one to the lexer until it yields a token. For instance:

        {[
          # let lexer = Lexer.create ();;
          val lexer : Lexer.t = <abstract>
          # Lexer.feed lexer '(';;
          - : [ `atom | `other ] Lexer.token = Lparen
          # Lexer.feed lexer ')';;
          - : [ `atom | `other ] Lexer.token = Rparen
        ]}

        When the lexer doesn't have enough to return a token, it simply returns
        the special token {!Lexer.Await}:

        {[
          # Lexer.feed lexer '1';;
          - : [ `atom | `other ] Lexer.token = Await
        ]}

        Note that since atoms of canonical S-expressions do not need quoting,
        they are always represented as a contiguous sequence of characters that
        don't need further processing. To achieve maximum efficiency, the lexer
        only returns the length of the atom and it is the responsibility of the
        caller to extract the atom from the input source:

        {[
          # Lexer.feed lexer '2';;
          - : [ `atom | `other ] Lexer.token = Await
          # Lexer.feed lexer ':';;
          - : [ `atom | `other ] Lexer.token = Atom 2
        ]}

        When getting [Atom n], the caller should then proceed to read the next
        [n] characters of the input as a string. For instance, if the input is
        an [in_channel] the caller should proceed with
        [really_input_string ic n].

        Finally, when the end of input is reached the user should call
        {!Lexer.feed_eoi} to make sure the lexer is not awaiting more input. If
        that is the case, {!Lexer.feed_eoi} will raise:

        {[
          # Lexer.feed lexer '1';;
          - : [ `atom | `other ] Lexer.token = Await
          # Lexer.feed_eoi lexer;;
          Exception: Parse_error "premature end of input".
        ]}

        {2 Parsing stacks}

        The lexer doesn't keep track of the structure of the S-expressions. In
        order to construct a whole structured S-expressions, the caller must
        maintain a parsing stack via the {!Stack} module. A {!Stack.t} value
        simply represent a parsed prefix in reverse order.

        For instance, the prefix "1:x((1:y1:z)" will be represented as:

        {[ Sexp (List [ Atom "y"; Atom "z" ], Open (Sexp (Atom "x", Empty))) ]}

        The {!Stack} module offers various primitives to open or close
        parentheses or insert an atom. And for convenience it provides a
        function {!Stack.add_token} that takes the output of {!Lexer.feed}
        directly:

        {[
          # Stack.add_token Rparen Empty;;
          - : Stack.t = Open Empty
          # Stack.add_token Lparen (Open Empty);;
          - : Stack.t = Sexp (List [], Empty)
        ]}

        Note that {!Stack.add_token} doesn't accept [Atom _]. This is enforced
        at the type level by a GADT. The reason for this is that in order to
        insert an atom, the user must have fetched the contents of the atom
        themselves. In order to insert an atom into a stack, you can use the
        function {!Stack.add_atom}:

        {[
          # Stack.add_atom "foo" (Open Empty);;
          - : Stack.t = Sexp (Atom "foo", Open Empty)
        ]}

        When parsing is finished, one may call the function {!Stack.to_list} in
        order to extract all the toplevel S-expressions from the stack:

        {[
          # Stack.to_list (Sexp (Atom "x", Sexp (List [Atom "y"], Empty)));;
          - : sexp list = [List [Atom "y"; Atom "x"]]
        ]}

        If instead you want to stop parsing as soon a single full S-expression
        has been discovered, you can match on the structure of the stack. If the
        stack is of the form [Sexp (_, Empty)], then you know that exactly one
        S-expression has been parsed and you can stop there.

        {2 Parsing errors}

        In order to reduce allocations to a minumim, parsing errors are reported
        via the exception {!Parse_error}. It is the responsibility of the caller
        to catch this exception and return it as an [Error _] value. Functions
        that may raise [Parse_error] are documented as such.

        When extracting an atom and the input doesn't have enough characters
        left, the user may raise [Parse_error premature_end_of_input]. This will
        produce an error message similar to what the various high-level
        functions of this library produce.

        {2 Building a parsing function}

        Parsing functions should always follow the following pattern:

        + create a lexer and start with an empty parsing stack
        + iterate over the input, feeding the lexer characters one by one. When
          the lexer returns [Atom n], fetch the next [n] characters from the
          input to form an atom
        + update the stack via [Stack.add_atom] or [Stack.add_token]
        + if parsing the whole input, call [Lexer.feed_eoi] when the end of
          input is reached, otherwise stop as soon as the stack is of the form
          [Sexp (_, Empty)] -

        For instance, to parse a string as a list of S-expressions:

        {[
          module Sexp = struct
            type t =
              | Atom of string
              | List of t list
          end

          module Csexp = Csexp.Make (Sexp)

          let extract_atom s pos len =
            match String.sub s pos len with
            | exception _ ->
              (* Turn out-of-bounds errors into [Parse_error] *)
              raise (Parse_error premature_end_of_input)
            | s -> s

          let parse_string =
            let open Csexp.Parser in
            let rec loop s pos len lexer stack =
              if pos = len then (
                Lexer.feed_eoi lexer;
                Stack.to_list stack
              ) else
                match Lexer.feed lexer (String.unsafe_get s pos) with
                | Atom atom_len ->
                  let atom = extract_atom s (pos + 1) atom_len in
                  loop s (pos + 1 + atom) len lexer (Stack.add_atom atom stack)
                | (Await | Lparen | Rparen) as x ->
                  loop s (pos + 1) len lexer (Stack.add_token x stack)
            in
            fun s ->
              match loop s 0 (String.length s) (Lexer.create ()) Empty with
              | v -> Ok v
              | exception Parse_error msg -> Error msg
        ]} *)

    exception Parse_error of string

    (** Error message signaling the end of input was reached prematurely. You
        can use this when extracting an atom from the input and the input
        doesn't have enough characters. *)
    val premature_end_of_input : string

    module Lexer : sig
      (** Lexical analyser *)

      type t

      val create : unit -> t

      type _ token =
        | Await : [> `other ] token
        | Lparen : [> `other ] token
        | Rparen : [> `other ] token
        | Atom : int -> [> `atom ] token

      (** Feed a character to the parser.

          @raise Parse_error *)
      val feed : t -> char -> [ `other | `atom ] token

      (** Feed the end of input to the parser.

          You should call this function when the end of input has been reached
          in order to ensure that the lexer is not awaiting more input, which
          would be an error.

          @raise Parse_error if the lexer is awaiting more input *)
      val feed_eoi : t -> unit
    end

    module Stack : sig
      (** Parsing stack *)

      type t =
        | Empty
        | Open of t
        | Sexp of sexp * t

      (** Extract the list of full S-expressions contained in a stack.

          For instance:

          {[
            # to_list (Sexp (Atom "y", Sexp (Atom "x", Empty)));;
            - : Stack.t list = [Atom "x"; Atom "y"]
          ]}
          @raise Parse_error if the stack contains open parentheses that has not
          been closed. *)
      val to_list : t -> sexp list

      (** Add a left parenthesis. *)
      val open_paren : t -> t

      (** Add a right parenthesis. Raise [Parse_error] if the stack contains no
          opened parentheses.

          For instance:

          {[
            # close_paren (Sexp (Atom "y", Sexp (Atom "x", Open Empty)));;
            - : Stack.t = Sexp (List [Atom "x"; Atom "y"], Empty)
          ]}
          @raise Parse_error if the stack contains no open open parenthesis. *)
      val close_paren : t -> t

      (** Insert an atom in the parsing stack:

          {[
            # add_atom "foo" Empty;;
            - : Stack.t = Sexp (Atom "foo", Empty)
          ]} *)
      val add_atom : string -> t -> t

      (** Add a token as returned by the lexer.

          @raise Parse_error *)
      val add_token : [ `other ] Lexer.token -> t -> t
    end
  end

  (** {3 Deprecated low-level parser} *)

  (** The above are deprecated as the {!Input} signature does not allow to
      distinguish between IO errors and end of input conditions. Additionally,
      the use of monads tend to produce parsers that allocates a lot.

      It is recommended to use the {!Parser} module instead. *)

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

module Make (Sexp : Sexp) : S with type sexp := Sexp.t

include Sexp

include S with type sexp := t
