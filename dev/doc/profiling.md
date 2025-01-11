# How to profile Rocq?

I (Pierre-Marie Pédrot) mainly use two OCaml branches to profile Rocq, whether I
want to profile time or memory consumption. AFAIK, this only works for Linux.

## Time

In Rocq source folder:

```
opam switch 4.09.0+trunk+fp
make world
perf record -g _build/install/default/bin/coqc file.v
perf report -g fractal,callee --no-children
```

To profile only part of a file, first load it using

```
bin/coqtop -l file.v
```

and plug into the process

```
perf record -g -p PID
```

### Per-component [flame graphs](https://github.com/brendangregg/FlameGraph)

I (Andres Erbsen) have found it useful to look at library-wide flame graphs of
rocq time consumption.  As the Ltac interpreter stack is reflected in the OCaml
stack, calls to the same primitive can appear on top of multiple essentially
equivalent stacks. To make the profiles more readable, one could either try to
edit the stack trace to merge "equivalent" frames, or simply look at the
aggregate profile on a component-by-component basis. Here is how to do the
second for the standard library ([example output](https://cdn.rawgit.com/andres-erbsen/b29b29cb6480dfc6a662062e4fcd0ae3/raw/304fc3fea9630c8e453929aa7920ca8a2a570d0b/stdlib_categorized_outermost.svg)).

```
#!/usr/bin/env bash
make clean
make states
perf record -F99  `# ~1GB of data` --call-graph=dwarf -- make world
perf script --time '0%-100%'  |
        stackcollapse-perf.pl |
        grep Coqtop__compile |
        sed -rf <(cat <<'EOF'
                s/;caml/;/g
                s/_[0-9]*;/;/g
                s/Logic_monad__fun;//g
                s/_apply[0-9];//g
                s/;System/@&@/
                s/;Hashcons/@&@/
                s/;Grammar/@&@/
                s/;Declaremods/@&@/
                s/;Tactics/@&@/
                s/;Pretyping/@&@/
                s/;Typeops/@&@/
                s/;Reduction/@&@/
                s/;Unification/@&@/
                s/;Evarutil/@&@/
                s/;Evd/@&@/
                s/;EConstr/@&@/
                s/;Constr/@&@/
                s/;Univ/@&@/
                s/;Ugraph/@&@/
                s/;UState/@&@/
                s/;Micromega/@&@/
                s/;Omega/@&@/
                s/;Auto/@&@/
                s/;Ltac_plugin__Tacinterp/@&@/
                s/;Ltac_plugin__Rewrite/@&@/
                s/[^@]*@;([^@]*)@/\1;\1/
                s/@//g
                :a; s/;([^;]+);\1;/;\1;/g;ta
EOF
        ) |
        flamegraph.pl
```

## Memory (memtrace)

[memtrace](https://github.com/janestreet/memtrace) is a client library
for OCaml's Memprof statistical memory profiler.

See this blog post for more details:
https://blog.janestreet.com/finding-memory-leaks-with-memtrace/

To profile a file, you need to install the `memtrace` library, then
recompile Rocq. We also recommend you make a copy of the .v file (if
working on the stdlib to avoid issues with artifacts.

The following command sequence will do all that:
```
opam install memtrace
dune build theories/Strings/Byte.vo  # to build deps of Byte
cp theories/Strings/Byte.v ./MyByte.v
MEMTRACE=trace-byte.tcr dune exec -- dev/shim/coqc MyByte.v
memtrace-viewer trace-byte.tcr
```
