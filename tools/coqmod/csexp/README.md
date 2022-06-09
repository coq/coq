Csexp - Canonical S-expressions
===============================

This project provides minimal support for parsing and printing
[S-expressions in canonical form][wikipedia], which is a very simple
and canonical binary encoding of S-expressions.

[wikipedia]: https://en.wikipedia.org/wiki/Canonical_S-expressions

Example
-------

```ocaml
# #require "csexp";;
# module Sexp = struct type t = Atom of string | List of t list end;;
module Sexp : sig type t = Atom of string | List of t list end
# module Csexp = Csexp.Make(Sexp);;
module Csexp :
  sig
    val parse_string : string -> (Sexp.t, int * string) result
    val parse_string_many : string -> (Sexp.t list, int * string) result
    val input : in_channel -> (Sexp.t, string) result
    val input_opt : in_channel -> (Sexp.t option, string) result
    val input_many : in_channel -> (Sexp.t list, string) result
    val serialised_length : Sexp.t -> int
    val to_string : Sexp.t -> string
    val to_buffer : Buffer.t -> Sexp.t -> unit
    val to_channel : out_channel -> Sexp.t -> unit
  end
# Csexp.to_string (List [ Atom "Hello"; Atom "world!" ]);;
- : string = "(5:Hello6:world!)"
```

The MIT License

Copyright (c) 2016 Jane Street Group, LLC <opensource@janestreet.com>

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
