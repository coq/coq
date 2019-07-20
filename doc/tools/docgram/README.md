# Grammar extraction tool for documentation

`doc_grammar` extracts Coq's grammar from `.mlg` files, edits it and inserts it in
chunks into `.rst` files.  The tool currently inserts Sphinx
`productionlist` constructs.  It also generates a file with `prodn` constructs
for the entire grammar, but updates to `tacn` and `cmd` constructs must be done
manually since the grammar doesn't have names for them as it does for
nonterminals.  There is an option to report which `tacn` and `cmd` were not
found in the `.rst` files.  `tacv` and `cmdv` constructs are not processed at all.

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
unprocessed grammar of the mlg files with less clutter.  Nonterminals that use
levels (`"5" RIGHTA` below) are modified, for example:

```
tactic_expr:
  [ "5" RIGHTA
    [ te = binder_tactic -> { te } ]
```

becomes

```
tactic_expr5: [
| binder_tactic
| tactic_expr4
]
```

2. The tool applies grammar editing operations specified by `common.edit_mlg` to
generate `editedGrammar`.

3. `orderedGrammar` gives the desired order for the nonterminals and productions
in the documented grammar.  Developers should edit this file to change the order.
`doc_grammar` updates `orderedGrammar` so it has the same set of nonterminals and productions
as `editedGrammar`.  The update process removes manually-added comments from
`orderedGrammar` while automatically-generated comments will be regenerated.

4. The tool applies further edits to the grammar specified by `productionlist.edit_mlg`,
then it updates the productionlists in the `.rst` files as specified by comments in the form
`.. insertgram <first nt> <last nt>`.  The edits are primarily to expand
`.mlg` constructs such as `LIST1` and `OPT` into separate productions.  The tool
generates `productionlistGrammar`, which has the entire grammar in the form of `productionlists`.

5. Using the grammar produced in step 3, the tool applies edits specified by
`prodn.edit_mlg` and generates `prodnGrammar`, representing each production as
a Sphinx `prodn` construct.  Differently-edited grammars are used because `prodn`
can naturally represent `LIST1 x SEP ','` whereas that is awkward for `productionlists`.

## How to use the tool

* `make doc_gram` updates `fullGrammar`.

* `make doc_gram_verify` verifies that `fullGrammar` is consistent with the `.mlg` files.
  This is for use by CI.

* `make doc_gram_rsts` updates the `*Grammar` and `.rst` files.

Changes to `fullGrammar`, `orderedGrammar` and the `.rsts` should be checked in to git.
The other `*Grammar` files should not.

### Command line arguments

The executable takes a list of `.mlg` and `.rst` files as arguments.  The tool
inserts the grammar into the `.rsts` as specified by comments in those files.
The order of the `.mlg` files affects the order of nonterminals and productions in
`fullGrammar`.  The order doesn't matter for the `.rst` files.

Specifying the `-verify` command line argument avoids updating any of the files,
but verifies that the current files are consistent.  This setting is meant for
use in CI; it will be up to each developer to include the changes to `*Grammar` and
the `.rst` files in their PRs when they've changed the grammar.

Other command line arguments:

* `-check-tacs` reports on differences in tactics between the `rsts` and the grammar

* `-check-cmds` reports on differences in commands between the `rsts` and the grammar

* `-no-warn` suppresses printing of some warning messages

* `-short` limits processing to updating/verifying only the `fullGrammar` file

* `-verbose` prints more messages about the grammar

* `-verify` described above

### Grammar editing scripts

The grammar editing scripts `*.edit_mlg` are similar in format to `.mlg` files stripped
of all OCaml features.  This is an easy way to include productions to match or add without
writing another parser.  The `DOC_GRAMMAR` token at the beginning of each file
signals the use of streamlined syntax.

Each edit file has a series of items in the form of productions.  Items are applied
in the order they appear.  There are two types of editing operations:

* Global edits - edit rules that apply to the entire grammar in a single operation.
  These are identified by using specific reserved names as the non-terminal name.

* Local edits - edit rules that apply to the productions of a single non-terminal.
  The rule is a local edit if the non-terminal name isn't reserved.  Individual
  productions within a local edit that begin with a different set of reserved names
  edit existing productions.  For  example `binders: [ | DELETE Pcoq.Constr.binders ]`
  deletes the production `binders: [ | Pcoq.Constr.binders]`

Productions that don't begin with a reserved name are added to the grammar,
such as `empty: [ | ]`, which adds a new non-terminal `empty` with an
empty production on the right-hand side.

Another example: `LEFTQMARK: [ | "?" ]` is a local edit that treats `LEFTQMARK` as
the name of a non-terminal and adds one production for it.  (We know that LEFTQMARK
is a token but doc_grammar does not.)  `SPLICE: [ | LEFTQMARK ]` requests replacing all
uses of `LEFTQMARK` anywhere in the grammar with its productions and removing the
non-terminal.  The combined effect of these two is to replace all uses of
`LEFTQMARK` with `"?"`.

Here are the current operations.  They are likely to be refined as we learn
what operations are most useful while we update the mlg files and documentation:

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

`EXPAND` - expands LIST0, LIST1, LIST* ... SEP and OPT constructs into
new non-terminals

### Local edits

`DELETE <production>` - removes the specified production from the grammar

`EDIT <production>` - modifies the specified production using the following tags
that appear in the specified production:

* `USE_NT <name>` LIST* - extracts LIST* as new nonterminal with the specified
  new non-terminal name

* `ADD_OPT <grammar symbol>` - looks for a production that matches the specified
  production **without** `<grammar_symbol>`.  If found, both productions are
  replaced with single production with `OPT <grammar_symbol>`

  The current version handles a single USE_NT or ADD_OPT per EDIT.

* `REPLACE` - (2 sequential productions) - removes `<oldprod>` and
  inserts `<newprod>` in its place.

```
| REPLACE <oldprod>
| WITH <newprod>
```

* (any other nonterminal name) - adds a new production (and possibly a new nonterminal)
to the grammar.

### `.rst` file updates

`doc_grammar` updates `.rst` files when it sees the following 3 lines

```
.. insertgram <start> <end>
.. productionlist:: XXX
```

The end of the existing `productionlist` is recognized by a blank line.

### Other details

The output identifies productions from plugins that aren't automatically loaded with
`(* XXX plugin *)` in grammar files and with `(XXX plugin)` in productionlists.
If desired, this mechanism could be extended to tag certain productions as deprecated,
perhaps in conjunction with a coqpp change.
