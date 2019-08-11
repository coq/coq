Gathering Statistics
====================

Stats.ml provides a simple mechanism for developers to gather statistics across
multiple runs of `coqc`, whether in a local build or in CI.  The initial
version counts how many times each parser production is invoked.  The code can
be adapted to gather other statistics.

When enabled, each `coqc` process generates a `<.v-filename>.stats` file in the
`$COQ_STATS_DIR` directory.  In addition, each `coqc` combines its data with
any other `*.stats` file it finds in that directory.  The end result after
multiple `coqc` runs is a single `*.stats` file.

The code uses file renaming to ensure correct results when multiple `coqc`
processes are running simultaneously.  The `<.v-filename>` prefix (which is
qualified relative to the current directory) is used as a convenient unique
filename.

Sample output (excerpt)
-----------------------

```
      0  simple_tactic:  "abstract" ssrdgens
   3224  simple_tactic:  "absurd" constr
     31  simple_tactic:  "admit"
    186  simple_tactic:  "apply"
 608313  simple_tactic:  "apply" LIST1 constr_with_bindings_arg SEP "," in_hyp_as
   2108  simple_tactic:  "apply" ssrapplyarg
```

How to run locally
------------------

  - `export COQ_STATS_DIR=.` - set the output directory for statistics files
  - delete any existing `*.stats` files in `$COQ_STATS_DIR` lest they be
    incorrectly added into the totals
  - run `coqc` on one or more `.v` files.  This could be a full make/dune build
    if you wish.
  - `make doc_gram` - generates a file `doc/tools/docgram/prodmap` needed for
    printing results (do this once per source tree or after changing the
    grammar in the `*.mlg` files).
  - `bin/print_stats <*.stats files>` - sums the named files and print results.
    This assumes it's run in the root directory of a local build tree so it can
    access the `prodmap` file.

How to run with CI
------------------

  - In `.gitlab-ci.yml`, uncomment the line `# - export COQ_STATS_DIR=$PWD`.
  - Statistics are currently generated for selected jobs (build:*, library:*
    and plugin:*).  Configuration is described below.
  - Do a push, wait for CI to complete.
  - Get the pipeline number from the GUI (not a job number!).
  - Run `tools/fetch_stats.sh $PIPELINE` to download statistics files
  - `bin/print_stats <*.stats files>`

Configuring which jobs are included in the statistics
-----------------------------------------------------

There are 3 places that filter which jobs are included in your statistics:
  - CI generates a `$CI_JOB_NAME.stats` file for each job that has or inherits
    these settings in `.gitlab-ci.yml`:

  ```
    script:
      - export COQ_STATS_DIR=$PWD
    after_script:
      - if [ `ls *.stats|wc -l` = 1 ]; then mv *.stats $CI_JOB_NAME.stats; fi
    artifacts:
      paths:
        - "*.stats"
  ```

  - `fetch_stats.sh` currently filters out jobnames that include `+` so it only
    fetches one of the 5 `build` jobs.
  - You can filter in the call to `print_stats` or delete some files

Parsing statistics
------------------

The instrumentation counts how many times each production in the `*.mlg` files
is recognized.  The set of `.mlg` files included is $DOC_MLGS, defined in
`Makefile.build` (which omits, for example, `g_ltac2.mlg`).
The productions include anonymous productions nested inside named
productions, for example:

```
  type_cstr:
    [ [ c=OPT [":"; c=lconstr -> { c } ] -> { Loc.tag ~loc c } ] ]
```

has the nested production `[":"; c=lconstr -> { c } ]`.  This appears as
`(type_cstr : 537):  ":" lconstr` in the output.  `537` is the line number in
the `.mlg`.

Notations add productions to the grammar at run time.  These are not currently
included in the statistics.

The output doesn't distinguish between keywords and identifiers.


Gathering other statistics
--------------------------

Create new routines in `Stats` to handle other statistics.  Eventually we may
need a mechanism to configure what statistics to collect rather than, say,
relying on source code changes to configure statistics.  We'll see whether
statistics-gathering is popular enough to merit the additional effort.

`Marshal.from_channel` calls are not inherently type-safe.  Make sure you
correctly update the returned type for the one in `Stats.unmarshal`.
