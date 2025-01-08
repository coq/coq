# Grammar extraction tool for documentation

`doc_grammar` extracts Coq's grammar from `.mlg` files, edits it and inserts it
into `.rst` files.  The tool inserts `prodn` directives for grammar productions.
It also updates `tacn` and `cmd` directives when they can be unambiguously matched to
productions of the grammar (in practice, that's probably almost always).
`tacv` and `cmdv` directives are not updated because matching them appears to require
human judgement.  `doc_grammar` generates a few files that may be useful to
developers and documenters.

The mlg grammars present several challenges to generating an accurate grammar
for documentation purposes:

* The 30+ mlg files don't define an overall order in which nonterminals should
  appear in a complete grammar.

* Even within a single mlg file, nonterminals and productions are often given
  in an order that's much different from what a reader of the documentation would
  expect.  In a small number of cases, changing the order in the mlg would change
  how some inputs are parsed, in particular when the order determines how to distinguish
  otherwise ambiguous inputs.

  Strictly speaking, that means our grammar is not a context free grammar even though
  we gloss over that distinction in the documentation.

* For a few nonterminals, some productions are only available if certain plugins
  are activated (e.g. SSR).  Readers should be informed about these.

* Some limited parts of the grammar are defined in OCaml, including lookahead symbols
  like `test_bracket_ident` and references to nonterminals in other files using
  qualified names such as `Prim.ident`.  A few symbols are defined multiple times,
  such as `scope` and `orient`.

## What the tool does

1. The tool reads all the `mlg` files and generates `fullGrammar`, which includes
    all the grammar without the actions for each production or the OCaml code.  This
    file is provided as a convenience to make it easier to examine the (mostly)
    unprocessed grammar of the mlg files with less clutter.  This step includes two
    transformations that rename some nonterminal symbols:

    First, nonterminals that use levels (`"5" RIGHTA` below) are modified, for example:

    ```
    ltac_expr:
      [ "5" RIGHTA
        [ ... ]
      [ "4"   ...
    ```

    becomes

    ```
    tactic_expr5: [
    | ...
    | tactic_expr4
    ]
    ```

    Second, nonterminals that are local to an .mlg will be renamed, if necessary, to
    make them unique.  For example, `strategy_level` is defined as a local nonterminal
    in both `g_prim.mlg` and in `extraargs.mlg`.  The nonterminal defined in the former
    remains `strategy_level` because it happens to be processed before the latter,
    in which the nonterminal is renamed to `EXTRAARGS_strategy_level` to make the local
    symbol unique.

    Nonterminals listed after `GLOBAL:` are global; otherwise they are local.

    References to renamed symbols are updated with the modified names.

    Note: the 4 SSR mlgs and ssreflect-proof-language.rst are currently excluded
    from processing (hard coded).

2. The tool applies grammar editing operations specified by `common.edit_mlg` to
    generate `editedGrammar`.

3. `orderedGrammar` gives the desired order for nonterminals and individual productions
    in the documented grammar.  Developers should edit this file only to reorder lines.
    `doc_grammar` updates `orderedGrammar` so it has the same set of nonterminals and productions
    as `editedGrammar` while retaining the previous ordering.  Since the position of
    new or renamed nonterminals is unspecified, they tend to show up in the wrong
    place in `orderedGrammar`, therefore users should review the output and make
    appropriate adjustments to the order.

    The update process removes manually-added comments from `orderedGrammar` while
    automatically-generated comments will be regenerated.

4. The tool updates the `.rst` files.  Comments in the form
    `.. insertprodn <first nt> <last nt>` indicate inserting the productions for a
    range of nonterminals (in `orderedGrammar` order).  `.. cmd::` and `.. tacn::`
    directives are updated using
    prefixes in the form `[a-zA-Z0-9_ ]+` from the directive and the
    grammar.  If there is unique match in the grammar, the directive is updated, if needed.
    Multiple matches or no match gives an error message.

5. For reference, the tool generates `prodnGrammar`, which has the entire grammar in the form of `prodns`.

6. If requested by command-line arguments `-check-cmds` or `-check-tacs`,
    the tool generates `prodnCommands` (for commands) and `prodnTactics` (for tactics).
    The former lists all commands that are under `command` in `orderedGrammar` and
    compares it to the `:cmd:` and `:cmdv:` given in the rst files.  The latter
    lists all tactics that are under `simple_tactic` in the grammar and compares it
    to the `:tacn:` and `:tacv:`.  The tags at the beginning of each line mean:

    - (no tag) - the grammar and the rst match exactly and uniquely
    - `-` - a grammar production that can't be matched to an rst file entry
    - `+` - an rst entry that doesn't match a grammar production
    - `v` - the rst entry is a `:cmdv:` or `:tacv:`
    - `?` - the match between the grammar and the rst files is not unique

    These command line arguments also generate error messages for commands and
    tactics that are in the grammar but not the documentation and vice versa.

## How to use the tool

* `make doc_gram` updates `fullGrammar`.

* `make doc_gram_verify` verifies that `fullGrammar`, `orderedGrammar` and `*.rst`
  are consistent with the `.mlg` files.  This is for use by CI.

* `make doc_gram_rsts` updates the `*Grammar` and `.rst` files.

* `make doc_gram_rsts DOCGRAMWARN=1` will additionally print warnings.

Changes to `fullGrammar`, `orderedGrammar` and `*.rst` should be checked in to git.
The `prodn*` and other `*Grammar` files should not.

### Command line arguments

The executable takes a list of `.mlg` and `.rst` files as arguments.  The tool
inserts the grammar into the `*.rst` as specified by comments in those files.
The order of the `.mlg` files affects the order of nonterminals and productions in
`fullGrammar`.  The order doesn't matter for the `.rst` files.

Specifying the `-verify` command line argument avoids updating any of the files,
but verifies that the current files are consistent.  This setting is meant for
use in CI; it will be up to each developer to include the changes to `*Grammar` and
the `.rst` files in their PRs when they've changed the grammar.

Other command line arguments:

* `-check-tacs` causes generation of `prodnTactics`

* `-check-cmds` causes generation of `prodnCommands`

* `-no-warn` suppresses printing of some warning messages

* `-no-update` puts updates to `fullGrammar` and `orderedGrammar` into new files named
  `*.new`, leaving the originals unmodified.  For use in Dune.

* `-short` limits processing to updating/verifying only the `fullGrammar` file

* `-verbose` prints more messages about the grammar

* `-verify` described above

### Grammar editing scripts

The grammar editing script `common.edit_mlg` is similar in format to `.mlg` files but stripped
of all OCaml features.  This is an easy way to include productions to match or add without
writing another parser.  The `DOC_GRAMMAR` token at the beginning of each file
signals the use of the streamlined syntax.

The edit file has a series of items in the form of productions.  Items are applied
in the order they appear.  There are two types of editing operations:

* Global edits - edit rules that apply to the entire grammar in a single operation.
  These are identified by using specific reserved names as the non-terminal name.

* Local edits - edit rules that apply to the productions of a single non-terminal.
  The rule is a local edit if the non-terminal name isn't reserved.  Individual
  productions within a local edit that begin with a different set of reserved names
  edit existing productions.  For  example `binders: [ | DELETE Procq.Constr.binders ]`
  deletes the production `binders: [ | Procq.Constr.binders]`

Productions that don't begin with a reserved name are added to the grammar,
such as `empty: [ | ]`, which adds a new non-terminal `empty` with an
empty production on the right-hand side.

Another example: `LEFTQMARK: [ | "?" ]` is a local edit that treats `LEFTQMARK` as
the name of a non-terminal and adds a production for it.  (We know that LEFTQMARK
is a token but doc_grammar does not.)  `SPLICE: [ | LEFTQMARK ]` requests replacing all
uses of `LEFTQMARK` anywhere in the grammar with its productions and removing the
non-terminal.  The combined effect of these two is to replace all uses of
`LEFTQMARK` with `"?"`.



Here are the current operations:

### Global edits

`DELETE` - deletes the specified non-terminals anywhere in the grammar.  Each
should appear as a separate production.  Useful for removing non-terminals that
only do lookahead that shouldn't be in the documentation.

`RENAME` - each production specifies an (old name, new name) pair of
non-terminals to rename.

`SPLICE` - requests replacing all uses of the nonterminals anywhere in the
grammar with its productions and removing the non-terminal. Each should appear
as a separate production.  (Doesn't work recursively; splicing for both
`A: [ | B ]` and `B: [ | C ]` must be done in separate SPLICE operations.)

`OPTINREF` - applies the local `OPTINREF` edit to every nonterminal

`REACHABLE` - suppresses the "Unreachable symbol" warning for the listed nonterminals
and any symbols reachable from them.

`NOTINRSTS` - suppresses the "Nonterminal <NT> not included in .rst files" messages for
the listed nonterminals.

### Local edits

`DELETE <production>` - removes the specified production from the grammar

`EDIT <production>` - modifies the specified production using the following tags
that appear in the specified production:

* `USE_NT <name>` LIST* - extracts LIST* as a new nonterminal with the specified
  new non-terminal name

* `ADD_OPT <grammar symbol>` - looks for a production that matches the specified
  production **without** `<grammar_symbol>`.  If found, both productions are
  replaced with single production with `OPT <grammar_symbol>`

  The current version handles a single USE_NT or ADD_OPT per EDIT.  These symbols
  may appear in the middle of the production given in the EDIT.

`APPENDALL <symbols>` - inserts <symbols> at the end of every production in
<edited_nt>.

`INSERTALL <symbols>` - inserts <symbols> at the beginning of every production in
<edited_nt>.

`REPLACE` - (2 sequential productions) - removes `<oldprod>` and
  inserts `<newprod>` in its place.

```
| REPLACE <oldprod>
| WITH <newprod>
```

`COPYALL <destination>` - creates a new nonterminal `<destination>` and copies
all the productions in the nonterminal to `<destination>`.

`MOVETO <destination> <production>` - moves the production to `<destination>` and,
 if needed, creates a new production <edited_nt> -> \<destination>.

`MOVEALLBUT <destination>` - moves all the productions in the nonterminal to `<destination>`
*except* for the productions following the `MOVEALLBUT` production in the edit script
(terminated only by the closing `]`).

`OPTINREF` - verifies that <edited_nt> has an empty production.  If so, it removes
the empty production and replaces all references to <edited_nt> throughout the
grammar with `OPT <edited_nt>`

`PRINT` <nonterminal> - prints the nonterminal definition at that point in
  applying the edits.  Most useful when the edits get a bit complicated to follow.

`(any other nonterminal name)` - adds a new production (and possibly a new nonterminal)
to the grammar.

### `.rst` file updates

`doc_grammar` updates `.rst` files where it sees the following 3 lines

```
.. insertprodn <start> <end>

.. prodn::
```

The end of the existing `prodn` is recognized by a blank line.

### Tagging productions

`doc_grammar` tags the origin of productions from plugins that aren't automatically
loaded.  In grammar files, they appear as `(* XXX plugin *)`.  In rsts, productions
generated by `.. insertprodn` will include where relevant three spaces as (a delimiter)
and a tag name after each production, which Sphinx will show on the far right-hand side
of the production.

The origin of a production can be specified explicitly in `common.edit_mlg` with the
`TAG name` appearing at the end of a production.  `name` must be in quotes if it
contains whitespace characters.  Some edit operations preserve the
tags, but others, such as `REPLACE ... WITH ...` do not.

A mapping from filenames to tags (e.g. "g_ltac2.mlg" is "Ltac2") is hard-coded as is
filtering to avoid showing tags for, say, Ltac2 productions from appearing on every
production in that chapter.

If desired, this mechanism could be extended to tag certain productions as deprecated,
perhaps in conjunction with a coqpp change.
