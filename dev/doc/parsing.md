# Parsing

Rocq's parser is based on Camlp5 using an extensible grammar.  Somewhat helpful
Camlp5 documentation is available [here](http://camlp5.github.io/doc/htmlc/grammars.html).
However, the Camlp5 code has been copied into the Rocq source tree and may differ
from the Camlp5 release.

Notable attributes of the parser include:

* The grammar is extensible at run time.  This is essential for supporting notations
  and optionally-loaded plugins that extend the grammar.

* The grammar is split into multiple source files.  Nonterminals can be local to a file
  or global.

* While 95% of the nonterminals and almost all the productions are defined in the grammar,
  a few are defined directly in OCaml code.  Since many developers have worked on the parser
  over the years, this code can be idiosyncratic, reflecting various coding styles.

* The parser is a recursive descent parser that, by default, only looks at the next token
  to make a parsing decision.  It's possible to hand-code additional lookahead where
  necessary by writing OCaml code.

* There's no code that checks whether a grammar is ambiguous or whether every production
  can be recognized.  Developers who modify the grammar may, in some cases, need to structure their
  added productions in specific ways to ensure that their additions are parsable and that they
  don't break existing productions.

## Contents ##

- [Grammars: `*.mlg` File Structure](#grammars-mlg-file-structure)
- [Grammars: Nonterminals and Productions](#grammars-nonterminals-and-productions)
  - [Alternate production syntax](#alternate-production-syntax)
- [Usage notes](#usage-notes)
  - [Other components](#other-components)
  - [Parsing productions](#parsing-productions)
  - [Lookahead](#lookahead)

## Grammars: `*.mlg` File Structure ##

Grammars are defined in `*.mlg` files, which `coqpp` compiles into `*.ml` files at build time.
`coqpp` code is in the `coqpp` directory.  `coqpp` uses yacc and lex to parse the grammar files.
You can examine its yacc and lex input files in `coqpp_lex.mll` and `coqpp_parse.mly` for
details not fully covered here.

In addition, there is a `doc_grammar` build utility that uses the `coqpp` parser to extract the
grammar, then edits and inserts it into the documentation.  This is described in
[`doc/tools/docgram/README.md`](../../doc/tools/docgram/README.md).
`doc_grammar` generates
[`doc/tools/docgram/fullGrammar`](../../doc/tools/docgram/fullGrammar),
which has the full grammar for Rocq
(not including some optionally-loaded plugins).  This may be easier to read since everything is
in one file and the parser action routines and other OCaml code are omitted.

`*.mlg` files contain the following types of nodes (See `node` in the yacc grammar).  This part is
very specific to Rocq (not so similar to Camlp5):

* OCaml code - OCaml code enclosed in curly braces, which is copied verbatim to the generated `*.ml` file

* Comments - comments in the `*.mlg` file in the form `(* … *)`, which are not copied
  to the generated `*.ml` file.  Comments in OCaml code are preserved.

* `DECLARE_PLUGIN "*_plugin"` - associates the file with a specific plugin, for example "ltac_plugin"

* `GRAMMAR EXTEND` - adds additional nonterminals and productions to the grammar and declares global
  nonterminals referenced in the `GRAMMAR EXTEND`:

  ```
  GRAMMAR EXTEND Gram
    GLOBAL:
      bignat bigint …;
    <nonterminal definitions>
  END
  ```

  Global nonterminals are declared in `pcoq.ml`, e.g. `let bignat = Entry.create "bignat"`.
  All the `*.mlg` files include `open Pcoq` and often its modules, e.g. `open Procq.Prim`.

  `GRAMMAR EXTEND` should be used only for large syntax additions.  To add new commands
  and tactics, use these instead:

  - `VERNAC COMMAND EXTEND` to add new commands
  - `TACTIC EXTEND` to add new tactics
  - `ARGUMENT EXTEND` to add new nonterminals

  These constructs provide essential semantic information that's provided in a more complex,
  less readable way with `GRAMMAR EXTEND`.

* `VERNAC COMMAND EXTEND` - adds new command syntax by adding productions to the
  `command` nonterminal.  For example:

  ```
  VERNAC COMMAND EXTEND ExtractionLibrary CLASSIFIED AS QUERY
  | [ "Extraction" "Library" ident(m) ]
    -> { extraction_library false m }
  END
  ```

  Productions here are represented with alternate syntax, described later.

  New commands should be added using this construct rather than `GRAMMAR EXTEND` so
  they are correctly registered, such as having the correct command classifier.

  TODO: explain "ExtractionLibrary", CLASSIFIED AS, CLASSIFIED BY, "{ tactic_mode }", STATE

* `VERNAC { … } EXTEND` - TODO.  A variant.  The `{ … }` is a block of OCaml code.

* `TACTIC EXTEND` - adds new tactic syntax by adding productions to `simple_tactic`.
  For example:

  ```
  TACTIC EXTEND btauto
  | [ "btauto" ] -> { Refl_btauto.Btauto.tac }
  END
  ```

  adds a new nonterminal `btauto`.

  New tactics should be added using this construct rather than `GRAMMAR EXTEND`.

  TODO: explain DEPRECATED, LEVEL (not shown)

* `ARGUMENT EXTEND` - defines a new nonterminal

  ```
  ARGUMENT EXTEND ast_closure_term
       TYPED AS type_info
       PRINTED BY { pp_ast_closure_term }
       INTERPRETED BY { interp_ast_closure_term }
       GLOBALIZED BY { glob_ast_closure_term }
       SUBSTITUTED BY { subst_ast_closure_term }
       RAW_PRINTED BY { pp_ast_closure_term }
       GLOB_PRINTED BY { pp_ast_closure_term }
    | [ term_annotation(a) constr(c) ] -> { mk_ast_closure_term a c }
  END
  ```

  See comments in `tacentries.mli` for partial information on the various
  arguments.

* `VERNAC ARGUMENT EXTEND` - (part of `argument_extend` in the yacc grammar) defines
  productions for a single nonterminal.  For example:

  ```
  VERNAC ARGUMENT EXTEND language
  PRINTED BY { pr_language }
  | [ "Ocaml" ] -> { let _ = warn_deprecated_ocaml_spelling () in Ocaml }
  | [ "OCaml" ] -> { Ocaml }
  | [ "Haskell" ] -> { Haskell }
  | [ "Scheme" ] -> { Scheme }
  | [ "JSON" ] -> { JSON }
  END
  ```

  TODO: explain PRINTED BY, CODE

* DOC_GRAMMAR - Used in `doc_grammar`-generated files to permit simplified syntax

Note that you can reverse engineer many details by comparing the `.mlg` input file with
the `.ml` generated by `coqpp`.

## Grammars: Nonterminals and Productions

Here's a simple nonterminal definition in the Camlp5 format:

  ```
  universe:
    [ [ IDENT "max"; "("; ids = LIST1 universe_expr SEP ","; ")" -> { ids }
      | u = universe_expr -> { [u] } ] ]
  ;
  ```

In which:
* `universe` is the nonterminal being defined
* productions are separated by `|` and, as a group, are enclosed in `[ [ … ] ];`
* `u = universe_expr` refers to the `universe_expr` nonterminal.  `u` is bound to
  the value returned by that nonterminal's action routine, which can be
  referred to in the action routine.  For `ids = LIST1 universe_expr SEP ","`,
  `ids` is bound to the list of values returned by `universe_expr`.
* `-> { … }` contains the OCaml action routine, which is executed when the production is recognized
  and returns a value
* Semicolons separate adjacent grammatical elements (nonterminals, strings or other constructs)

Grammatical elements that appear in productions are:

- nonterminal names - identifiers in the form `[a-zA-Z0-9_]*`.  These correspond to variables in
  the generated `.ml` code.  In some cases a qualified name, such as `Prim.name`, is used.
- `"…"` - a literal string that becomes a keyword and cannot be used as an `ident`.
  The string doesn't have to be a valid identifier; frequently the string will contain only
  punctuation characters.  Generally we try to avoid adding new keywords that are also valid
  identifiers--though there is an unresolved debate among the developers about whether having more
  such keywords in general is good (e.g. it makes it easier to highlight keywords in GUIs)
  or bad (more keywords for the user to avoid and new keywords may require changes to existing
  proof files).
- `IDENT "…"` - a literal string that has the form of an `ident` that doesn't become
  a keyword
- `OPT element` - optionally include `element` (e.g. a nonterminal, IDENT "…" or "…").
  The value is of type `'a option`.
- `LIST1 element` - a list of one or more `element`s.  The value is of type `'a list`.
- `LIST0 element` - an optional list of `element`s
- `LIST1 element SEP sep` - a list of `element`s separated by `sep`
- `LIST0 element SEP sep` - an optional list of `element`s separated by `sep`
- `( elements )` - grouping to represent a series of elements as a unit,
  useful within `OPT` and `LIST*`.
- `[ elements1 | elements2 | … ]` - alternatives (either `elements1` or `elements2` or …),
  actually nested productions, each of which can have its own action routines

Nonterminals can also be defined with multiple levels to specify precedence and associativity
of its productions.  This is described in the Rocq documentation under the `Print Grammar`
command.  The first square bracket around a nonterminal definition is for grouping
level definitions, which are separated with `|`, for example:

  ```
  ltac_expr:
      [ "5" RIGHTA
        [ te = binder_tactic -> { te } ]
      | "4" LEFTA
      :
  ```

Grammar extensions can specify what level they are modifying, for example:

  ```
  ltac_expr: LEVEL "1" [ RIGHTA
    [ tac = ltac_expr; intros = ssrintros_ne -> { tclintros_expr ~loc tac intros }
    ] ];
  ```

### Alternate production syntax ###

Except for `GRAMMAR EXTEND`, the `EXTEND` nodes in the `*.mlg`s use simplified syntax in
productions that's similar to what's used in the `Tactic Notation` and
`Ltac2 Notation` commands.  For example:

  ```
  TACTIC EXTEND cc
  | [ "congruence" ] -> { congruence_tac 1000 [] }
  | [ "congruence" integer(n) ] -> { congruence_tac n [] }
  | [ "congruence" "with" ne_constr_list(l) ] -> { congruence_tac 1000 l }
  | [ "congruence" integer(n) "with" ne_constr_list(l) ] ->
     { congruence_tac n l }
  END
  ```

Nonterminals appearing in the alternate production syntax are accessed through `wit_*` symbols
defined in the OCaml code.  Some commonly used symbols are defined in `stdarg.ml`.
Others are defined in the code generated by `ARGUMENT EXTEND` and `VERNAC ARGUMENT EXTEND`
constructs.  References to nonterminals that don't have `wit_*` symbols cause
compilation errors.

The differences are:
* The outer `: [ … ];` is omitted.  Each production is enclosed in `| [ … ]`.
* The action routine is outside the square brackets
* Literal strings that are valid identifiers don't become reserved keywords
* No semicolons separating elements of the production
* `integer(n)` is used to bind a nonterminal value to a variable instead of `n = integer`
* Alternate forms of constructs are used:
  * `ne_entry_list` for `LIST1 entry`
  * `entry_list` for `LIST0 entry`
  * `ne_entry_list_sep(var, sep)` for `LIST1 entry SEP sep` where the list is bound to `var`
  * `entry_list_sep(var, sep)` for `LIST0 entry SEP sep` where the list is bound to `var`
  * `entry_opt` for OPT entry
* There's no way to define `LEVEL`s
* There's no equivalent to `( elements )` or `[ elements1 | elements2 | … ]`, which may
  require repeating similar syntax several times.  For example, this single production
  is equivalent to 8 productions in `TACTIC EXTEND` representing all possible expansions of
  three `OPT`s:

  ```
  | IDENT "Add"; IDENT "Parametric"; IDENT "Relation"; LIST0 binder; ":"; constr; constr;
          OPT [ IDENT "reflexivity"; IDENT "proved"; IDENT "by"; constr -> { … } ];
          OPT [ IDENT "symmetry"; IDENT "proved"; IDENT "by"; constr -> { … } ];
          OPT [ IDENT "transitivity"; IDENT "proved"; IDENT "by"; constr -> { … } ];
          IDENT "as"; ident -> { … }
  ```

## Usage notes

### Other components

Rocq's lexer is in `clexer.ml`.  Its 10 token types are defined in `tok.ml`.

The parser is in `grammar.ml`.  The extensive use of GADT (generalized algebraic datatypes)
makes it harder for the uninitiated to understand it.

When the parser is invoked, the call tells the parser which nonterminal to parse.  `vernac_control`
is the start symbol for commands.  `tactic_mode` is the start symbol for tactics.
Tactics give syntax errors if Rocq is not in proof mode.  There are additional details
not mentioned here.

### Parsing productions

Some thoughts, not to be taken as identifying all the issues:

Since the parser examines only the next token to make a parsing decision (and perhaps
because of other potentially fixable limitations), some productions have to be ordered
or structured in a particular way to parse correctly in all cases.

For example, consider these productions:

  ```
  command: [ [
    | IDENT "Print"; p = printable -> { VernacPrint p }
    | IDENT "Print"; qid = smart_global; l = OPT univ_name_list -> { VernacPrint (PrintName (qid,l)) }
    | IDENT "Print"; IDENT "Module"; "Type"; qid = global ->
        { VernacPrint (PrintModuleType qid) }
    | IDENT "Print"; IDENT "Module"; qid = global ->
        { VernacPrint (PrintModule qid) }
    | IDENT "Print"; IDENT "Namespace" ; ns = dirpath ->
        { VernacPrint (PrintNamespace ns) }
    :

  printable:
    [ [ IDENT "Term"; qid = smart_global; l = OPT univ_name_list -> { PrintName (qid,l) }
      | IDENT "All" -> { PrintFullContext }
      | IDENT "Section"; s = global -> { PrintSectionContext s }
      :
  ```

Reversing the order of the first two productions in `command` causes the `All` in `Print All` to
be parsed incorrectly as a `smart_global`, making that command unavailable.  `Print Namespace nat.`
still works correctly, though.

Similarly, the production for `Print Module Type` has to appear before `Print Module <global>`
in order to be reachable.

Internally, the parser generates a tree that represents the possible prefixes for the
productions of a nonterminal as described in
[the Camlp5 documentation](http://camlp5.github.io/doc/htmlc/grammars.html#b:Rules-insertion).

Here's another example in which the way the productions are written matters.  `OPT` at
the beginning of a production doesn't always work well:

  ```
  command: [ [
      | IDENT "Foo"; n = natural -> { VernacBack 1 }
      | OPT (IDENT "ZZ"); IDENT "Foo" -> { VernacBack 1 }
      :
  ```

`Foo.` looks like it should be accepted, but it gives a parse error:

  ```
  Unnamed_thm < Foo.
  Toplevel input, characters 3-4:
  > Foo.
  >    ^
  Error:
  Syntax error: [prim:natural] expected after 'Foo' (in [vernac:command]).
  ```

Reversing the order of the productions doesn't help, but splitting
the 'OPT' production into 2 productions works:

  ```
      | IDENT "Foo" -> { VernacBack 1 }
      | IDENT "ZZ"; IDENT "Foo" -> { VernacBack 1 }
      | IDENT "Foo"; n = natural -> { VernacBack 1 }

  ```

On the other hand, `OPT` works just fine when the parser has already found the
right production.  For example `Back` and `Back <natural>` can be combined using
an `OPT`:

  ```
      | IDENT "Back"; n = OPT natural -> { VernacBack (Option.default 1 n) }
  ```

### Lookahead

It's possible to look ahead more than one symbol using OCaml code.  Generally we
avoid doing this unless there's a strong reason to do so.  For example, this
code defines a new nonterminal `local_test_lpar_id_colon` that checks that
the next 3 tokens are `"("` `ident` and `":"` without consuming any input:

  ```
  let local_test_lpar_id_colon =
    let open Procq.Lookahead in
    to_entry "lpar_id_colon" begin
      lk_kw "(" >> lk_ident >> lk_kw ":"
    end
  ```

This one checks that the next 2 tokens are `"["` and `"|"` with no space between.
This is a special case: intropatterns can have sequences like `"[|]"` that are
3 different tokens with empty nonterminals between them.  Making `"[|"` a keyword
would break existing code with "[|]":

  ```
  let test_array_opening =
    let open Procq.Lookahead in
    to_entry "test_array_opening" begin
      lk_kw "[" >> lk_kw "|" >> check_no_space
    end
  ```

TODO: how to add a tactic or command
