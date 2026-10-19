#!/usr/bin/env bash
# Print Assumptions reuses traversals across queries in one environment. The
# reuse must not cost more time, stack or memory than the walk it replaces.
# The files are generated here and compiled with -R . P, as real libraries
# are.
#
# Time: one user name reached under two canonical names. A chain of 8,000
# definitions over an object of a module alias is queried alternately with a
# constant whose implementation, read through a sealed functor application,
# reaches the same user name under the other canonical name.
# - Flip8000: c(k) := S c(k-1) over M2.bar with M2 := M, queried with P2.bar
#   for P2 := N M2.
# - AliasChain8000: y(k) := S y(k-1) over MA.c with MA := M, queried with
#   z := Q.c for Q := F MA.
# - BlockChain8000: the same with an inductive in place of the constant:
#   z(k) := S z(k-1) over a match on MA.c0, queried with Q.d, whose
#   implementation matches on X.c0.
# Compiling each file must take at most three times the CPU time of compiling
# it without its queries, plus one second; the walk without reuse takes about
# as long either way. A cache that replaces the entry recorded under one
# canonical name by one under the other, for a constant or for the members of
# an inductive block, makes every later replay of the chain go down to that
# name and miss, at each level: about ten times as long here. Measuring both
# compilations in the same run makes the check independent of the machine's
# speed.
#
# Stack and memory, with an 8 MiB stack (ulimit -s 8192) and 2 GB of address
# space (ulimit -v 2000000):
# - Chain50000, Chain72500: Definition x(k) := S x(k-1) over Axiom A.
# - Fan100000: that chain to 100,000, then a balanced tree of [f a b := a]
#   over x10, x20, ..., x100000, queried twice; the second query is a replay.
# - IndChain28000: Inductive I(k) := c(k) : I(k-1) -> I(k) over Axiom B.
# - MixChain23000: Definition e(k) := J(k-1) alternating with
#   Inductive J(k) := k(k) : e(k) -> J(k).
# - Wide40000: one inductive with 40,000 constructors, queried twice. The
#   walk without reuse needs about 0.8 GB of address space; a replay that
#   pushes a block's shared edges once per member runs out even at 4 GB.
# Every size answers without reuse on the dev profile (what `make world` and
# CI build) and on the release profile (-O3, as `dune build -p` builds),
# whose larger frames lower the inductive limits to about 29,000 inductives
# and 23,750 mixed links. The definition chains catch a non-tail call into
# the walk, which overflows from about 47,500 definitions on the dev profile,
# and Fan100000's second query a recursive replay. A walk frame one slot
# larger than without reuse shortens the longest definition chain that
# answers on the release profile from about 74,700 to about 65,000, which
# Chain72500 catches; the inductive limits it shortens less, so frame sizes
# are also checked on the object code (objdump), not by this script alone.
#
# Memory kept between queries, with an 8 MiB stack and 1,000,000 KiB of
# address space (ulimit -v 1000000):
# - Retain64: 64 groups of 100 definitions with one 1,000-argument body
#   F b0 ... b999, each group under a root G(g); G0 ... G63 are queried in
#   turn, so the queries share only F and the b's.
# - BlockRetain64: the same with groups of 100 inductives whose constructors
#   take that body.
# The walk without reuse drops each query's data before the next; the reuse
# keeps entries, and clears them when they weigh more than twice the
# heaviest query. Measured on the dev and the release profile, both files
# need 720 to 790 MiB of address space without reuse, 790 to 880 MiB with the
# bounded reuse, and 1,240 to 1,280 MiB with a cache that keeps every entry
# until the environment changes, which runs out here.
#
# Constants without a body (axioms, parameters, Admitted lemmas) whose types
# name many objects. The walk without reuse keeps no reference of such a type
# (the constant maps to None), so the reuse must keep none either, and a
# replay must not hold them all at once: a set per constant, which
# hash-consing makes cheap for the environment, costs the product of the two
# counts. Each case answers without reuse under its cap on the dev and the
# release profile (peak RSS 340 to 640 MB).
# - AxMod2000: 2,000 modules A(k) : S, S holding Parameter a : T, T naming
#   2,000 definitions through BIG; one query, under -v 1000000. AxOne2000 and
#   AdmOne1300: 2,000 Axioms, or 1,300 Lemmas proved by Admitted, of type
#   BIG = 0, BIG naming as many definitions; one query, under -v 1000000.
#   They run out of memory when each constant keeps a set of the references
#   of its type.
# - AxChain3000: z(k) : idT (z(k-1) 0 p) -> BIG = 0 -> nat for 3,000 axioms,
#   BIG naming 3,000 definitions, queried twice, under -v 800000. The second
#   query replays the chain, and runs out of memory when the replay queues
#   the references of the type of every link again (3,000 x 3,000 list
#   cells), as it does when it collects them without remembering which it
#   queued.
# - AxLibQ2: a library of 2,000 axioms a(k) : BIG, BIG naming 2,000 axioms
#   b(k), and a client that queries a root R over all of them twice, under
#   -v 1000000: the second query replays 2,000 axioms. Its CPU time must be
#   at most three times the first's plus one second, which is measured on
#   three clients of the one library (no query, one, two) so that the
#   machine's speed does not matter.
#
# OCaml 5 ignores ulimit -s (it runs OCaml code on its own stack), and the
# memory caps were measured on OCaml 4 only: the stack and memory cases are
# skipped there, rather than pass on files that cannot overflow.

set -e

export PATH=$BIN:$PATH
export LC_ALL=C

case $(rocq --version) in
  *"compiled with OCaml 4."*) ocaml4=true ;;
  *) ocaml4=false ;;
esac

cd misc
rm -rf print-assumptions-cache-limits
mkdir print-assumptions-cache-limits
cd print-assumptions-cache-limits

status=0

# Prints the output of $2 when it differs from $3, and fails.
expect() {
  if [ "$2" != "$3" ]; then
    echo "$1: unexpected output:"
    echo "$2"
    status=1
  fi
}

flip() {
  echo "Axiom foo : nat."
  echo "Module Type T. Parameter bar : nat. End T."
  echo "Module M : T. Module Hide. Definition x := foo. End Hide. Definition bar := Hide.x. End M."
  echo "Module M2 := M."
  echo "Module N (X : T) : T. Definition y := X.bar. Definition bar := y. End N."
  echo "Module P2 := N M2."
  echo "Definition c0 := M2.bar."
  for ((k = 1; k <= $1; k++)); do echo "Definition c$k := S c$((k - 1))."; done
  for _ in 1 2; do echo "Print Assumptions c$1."; echo "Print Assumptions P2.bar."; done
}

aliaschain() {
  echo "Axiom ax : nat."
  echo "Module Type T. Parameter c : nat. End T."
  echo "Module M : T. Definition c := ax. End M."
  echo "Module MA := M."
  echo "Module F (X : T) : T. Definition c := X.c. End F."
  echo "Module Q := F MA."
  echo "Definition y0 := MA.c."
  for ((k = 1; k <= $1; k++)); do echo "Definition y$k := S y$((k - 1))."; done
  echo "Definition z := Q.c."
  for _ in 1 2; do echo "Print Assumptions y$1."; echo "Print Assumptions z."; done
}

blockchain() {
  echo "Axiom ax : nat."
  echo "Module Type T. Inductive I := c0 : nat -> I. End T."
  echo "Module M : T. Inductive I := c0 : nat -> I. End M."
  echo "Module MA := M."
  echo "Module Type T2. Parameter d : nat. End T2."
  echo "Module F (X : T) : T2. Definition d := match X.c0 ax with X.c0 k => k end. End F."
  echo "Module Q := F MA."
  echo "Definition z0 := match MA.c0 ax with MA.c0 k => k end."
  for ((k = 1; k <= $1; k++)); do echo "Definition z$k := S z$((k - 1))."; done
  for _ in 1 2; do echo "Print Assumptions z$1."; echo "Print Assumptions Q.d."; done
}

# Compiles $1 under a CPU cap, leaving its output in $1.log, and prints its
# CPU seconds (user + system).
cpu() {
  local TIMEFORMAT='%U %S' t
  t=$( { time (ulimit -t 300; rocq c -q -R . P "$1" > "$1.log" 2>&1); } 2>&1 ) || true
  awk -v t="$t" 'BEGIN { split(t, a, " "); printf "%.2f", a[1] + a[2] }'
}

flip 8000 > Flip8000.v
aliaschain 8000 > AliasChain8000.v
blockchain 8000 > BlockChain8000.v

for f in Flip8000 AliasChain8000 BlockChain8000; do
  grep -v '^Print Assumptions' "$f.v" > "${f}NoQuery.v"
  full=$(cpu "$f.v")
  base=$(cpu "${f}NoQuery.v")
  case $f in
    Flip*) axiom='foo : nat' ;;
    *) axiom='ax : nat' ;;
  esac
  want="Axioms:
$axiom
Axioms:
$axiom
Axioms:
$axiom
Axioms:
$axiom"
  expect "$f" "$(cat "$f.v.log")" "$want"
  expect "${f}NoQuery" "$(cat "${f}NoQuery.v.log")" ""
  if ! awk -v f="$full" -v b="$base" 'BEGIN { exit !(f <= 3 * b + 1) }'; then
    echo "$f: ${full}s of CPU, against ${base}s without its queries"
    status=1
  fi
done

if ! $ocaml4; then
  echo "Skipping the stack and memory cases: not built with OCaml 4, whose limits they are measured against."
  exit $status
fi

chain() {
  echo "Axiom A : nat."
  echo "Definition x0 := A."
  echo "Definition f (a b : nat) := a."
  for ((k = 1; k <= $1; k++)); do echo "Definition x$k := S x$((k - 1))."; done
}

tree() {
  # balanced tree of f over the given leaves
  if [ "$#" -eq 1 ]; then printf '%s' "$1"; return; fi
  local half=$(($# / 2))
  printf '(f '
  tree "${@:1:half}"
  printf ' '
  tree "${@:half+1}"
  printf ')'
}

indchain() {
  echo "Unset Elimination Schemes."
  echo "Axiom B : Type."
  echo "Inductive I0 : Type := c0 : B -> I0."
  for ((k = 1; k <= $1; k++)); do echo "Inductive I$k : Type := c$k : I$((k - 1)) -> I$k."; done
  echo "Print Assumptions I$1."
}

mixchain() {
  echo "Unset Elimination Schemes."
  echo "Axiom B : Type."
  echo "Inductive J0 : Type := k0 : B -> J0."
  for ((k = 1; k <= $1; k++)); do
    echo "Definition e$k := J$((k - 1))."
    echo "Inductive J$k : Type := k$k : e$k -> J$k."
  done
  echo "Print Assumptions J$1."
}

wide() {
  echo "Unset Elimination Schemes."
  echo "Inductive wide : Set :="
  for ((k = 0; k < $1; k++)); do echo "| C$k : wide"; done
  echo "."
  echo "Print Assumptions wide."
  echo "Print Assumptions wide."
}

# Q groups of M definitions with one shared body, F b0 ... b(K-1), and a root
# G(g) over its group's definitions; G0 ... G(Q-1) are queried in turn, so the
# queries share only F and the b's.
retain() {
  local k=$1 m=$2 q=$3 g j args xs bs zeros
  xs=$(seq -f 'x%g' 0 $((k - 1)) | tr '\n' ' ')
  bs=$(seq -f 'b%g' 0 $((k - 1)) | tr '\n' ' ')
  zeros=$(yes 0 | head -n $((k - m)) | tr '\n' ' ')
  echo "Axiom ax : nat."
  echo "Definition F (${xs}: nat) : nat := 0."
  seq -f 'Definition b%g := ax.' 0 $((k - 1))
  echo "Abbreviation BIG := (F ${bs% })."
  for ((g = 0; g < q; g++)); do
    args=""
    for ((j = 0; j < m; j++)); do echo "Definition d${g}_$j := BIG."; args+="d${g}_$j "; done
    echo "Definition G$g := F $args${zeros% }."
  done
  for ((g = 0; g < q; g++)); do echo "Print Assumptions G$g."; done
}

# The same with inductive blocks: group g holds M inductives whose
# constructors take a BIG, and G(g) is their product.
blockretain() {
  local k=$1 m=$2 q=$3 g j xs bs prod
  xs=$(seq -f 'x%g' 0 $((k - 1)) | tr '\n' ' ')
  bs=$(seq -f 'b%g' 0 $((k - 1)) | tr '\n' ' ')
  echo "Unset Elimination Schemes."
  echo "Axiom ax : nat."
  echo "Definition F (${xs}: nat) : Set := nat."
  seq -f 'Definition b%g := ax.' 0 $((k - 1))
  echo "Abbreviation BIG := (F ${bs% })."
  for ((g = 0; g < q; g++)); do
    prod=""
    for ((j = 0; j < m; j++)); do
      echo "Inductive I${g}_$j : Set := c${g}_$j : BIG -> I${g}_$j."
      prod+="I${g}_$j * "
    done
    echo "Definition G$g := (${prod% \* })%type."
  done
  for ((g = 0; g < q; g++)); do echo "Print Assumptions G$g."; done
}

# The names of seq format $1, from 1 to $2, on one line.
names() { seq -f "$1" 1 "$2" | tr '\n' ' '; }

# Constants without a body whose types name $1 definitions, one query over
# all of them. [axmod]: $1 modules A(k) : S, S holding one Parameter of that
# type. [axone]: $1 Axioms (or Lemmas proved by Admitted) of type BIG = 0, one
# command each, taken by a definition H.
axmod() {
  seq -f 'Definition c%g := 0.' 1 $1
  echo "Abbreviation BIG := ($(seq -f 'c%g' 1 $1 | paste -sd+ | sed 's/+/ + /g'))."
  echo "Module Type S. Parameter a : (fun _ : nat => nat) BIG. End S."
  seq -f 'Declare Module A%g : S.' 1 $1
  echo "Definition all : nat := $(seq -f 'A%g.a' 1 $1 | paste -sd+ | sed 's/+/ + /g')."
  echo "Print Assumptions all."
}

axone() {
  echo "Definition F ($(names 'x%g' $1): nat) : nat := 0."
  seq -f 'Definition b%g := 0.' 1 $1
  echo "Abbreviation BIG := (F $(names 'b%g' $1))."
  echo "Definition T := BIG = 0."
  echo "Definition H ($(names 'y%g' $1): T) : nat := 0."
  if [ "$2" = Admitted ]; then seq -f 'Lemma a%g : BIG = 0. Proof. Admitted.' 1 $1
  else seq -f 'Axiom a%g : BIG = 0.' 1 $1; fi
  echo "Definition G := H $(names 'a%g' $1)."
  echo "Print Assumptions G."
}

# A library of $1 axioms a(k) of type BIG, which names the $1 axioms b(k)
# through G, and a root R: a balanced tree of [f] over all the a(k).
axlib() {
  echo "Axiom G : $(yes 'nat ->' | head -n $1 | tr '\n' ' ')Prop."
  seq -f 'Axiom b%g : nat.' 1 $1
  echo "Abbreviation BIG := (G $(names 'b%g' $1))."
  seq -f 'Axiom a%g : BIG.' 1 $1
  echo "Definition f (x y : BIG) : BIG := x."
  local leaves=() k
  for ((k = 1; k <= $1; k++)); do leaves+=("a$k"); done
  echo "Definition R := $(tree "${leaves[@]}")."
}

{ chain 50000; echo "Print Assumptions x50000."; } > Chain50000.v
{ chain 72500; echo "Print Assumptions x72500."; } > Chain72500.v
leaves=()
for ((k = 10; k <= 100000; k += 10)); do leaves+=("x$k"); done
{ chain 100000; printf 'Definition R := '; tree "${leaves[@]}"; echo "."
  echo "Print Assumptions R."; echo "Print Assumptions R."; } > Fan100000.v
indchain 28000 > IndChain28000.v
mixchain 23000 > MixChain23000.v
wide 40000 > Wide40000.v

axiom_a='Axioms:
A : nat'
axiom_b='Axioms:
B : Type'
closed='Closed under the global context'

for f in Chain50000 Chain72500 Fan100000 IndChain28000 MixChain23000 Wide40000; do
  out=$(ulimit -s 8192; ulimit -v 2000000; rocq c -q -R . P "$f.v" 2>&1) || true
  case $f in
    Fan100000) want="$axiom_a
$axiom_a" ;;
    IndChain*|MixChain*) want=$axiom_b ;;
    Wide*) want="$closed
$closed" ;;
    *) want=$axiom_a ;;
  esac
  expect "$f" "$out" "$want"
done

retain 1000 100 64 > Retain64.v
blockretain 1000 100 64 > BlockRetain64.v
want=$(for ((g = 0; g < 64; g++)); do echo "Axioms:"; echo "ax : nat"; done)
for f in Retain64 BlockRetain64; do
  out=$(ulimit -s 8192; ulimit -v 1000000; rocq c -q -R . P "$f.v" 2>&1) || true
  expect "$f" "$out" "$want"
done

# The axioms are printed newest first, an order the case does not pin: the
# lines are compared sorted.
axmod 2000 > AxMod2000.v
axone 2000 Axiom > AxOne2000.v
axone 1300 Admitted > AdmOne1300.v
for f in AxMod2000 AxOne2000 AdmOne1300; do
  case $f in
    AxMod*) want=$({ echo "Axioms:"; seq -f 'A%g.a : (fun _ : nat => nat) BIG' 1 2000; } | sort) ;;
    AdmOne*) want=$({ echo "Axioms:"; seq -f 'a%g : BIG = 0' 1 1300; } | sort) ;;
    *) want=$({ echo "Axioms:"; seq -f 'a%g : BIG = 0' 1 2000; } | sort) ;;
  esac
  out=$(ulimit -s 8192; ulimit -v 1000000; rocq c -q -R . P "$f.v" 2>&1 | sort) || true
  expect "$f" "$out" "$want"
done

# A chain of $1 axioms over one wide type: z(k) : idT (z(k-1) 0 p) -> BIG = 0
# -> nat, BIG naming $1 definitions, two queries on the last link.
axchain() {
  echo "Definition F ($(names 'x%g' $1): nat) : nat := 0."
  seq -f 'Definition b%g := 0.' 1 $1
  echo "Abbreviation BIG := (F $(names 'b%g' $1))."
  echo "Definition idT (x : nat) : Set := nat."
  echo "Axiom p : BIG = 0."
  echo "Axiom z0 : nat -> BIG = 0 -> nat."
  local k
  for ((k = 1; k < $1; k++)); do echo "Axiom z$k : idT (z$((k - 1)) 0 p) -> BIG = 0 -> nat."; done
  for _ in 1 2; do echo "Print Assumptions z$(($1 - 1))."; done
}

axchain 3000 > AxChain3000.v
block=$({ echo "Axioms:"; echo "z0 : nat -> BIG = 0 -> nat"
          for ((k = 1; k < 3000; k++)); do echo "z$k : idT (z$((k - 1)) 0 p) -> BIG = 0 -> nat"; done
          echo "p : BIG = 0"; } | sort)
want=$({ echo "$block"; echo "$block"; } | sort)
out=$(ulimit -s 8192; ulimit -v 800000; rocq c -q -R . P AxChain3000.v 2>&1 | sort) || true
expect AxChain3000 "$out" "$want"

# A library of 2,000 axioms of a wide type, compiled once, and a client that
# queries a root over all of them twice, under the memory cap. The second
# query replays what the first recorded: its CPU time, from the clients with
# one and with no query, must be at most three times the first's plus one
# second.
axlib 2000 > Lib.v
expect Lib "$(rocq c -q -R . P Lib.v 2>&1)" ""
for n in 0 1 2; do
  { echo "Require Import P.Lib."; for ((k = 0; k < n; k++)); do echo "Print Assumptions R."; done; } > AxLibQ$n.v
done
out=$(ulimit -s 8192; ulimit -v 1000000; rocq c -q -R . P AxLibQ2.v 2>&1 | grep -E '^(Axioms:|[ab][0-9]+ : )' | sort) || true
want=$({ echo "Axioms:"; seq -f 'a%g : BIG' 1 2000; seq -f 'b%g : nat' 1 2000; } | sort)
want=$({ echo "$want"; echo "$want"; } | sort)
expect AxLibQ2 "$out" "$want"
c0=$(cpu AxLibQ0.v); c1=$(cpu AxLibQ1.v); c2=$(cpu AxLibQ2.v)
if ! awk -v c0="$c0" -v c1="$c1" -v c2="$c2" 'BEGIN { exit !(c2 - c1 <= 3 * (c1 - c0) + 1) }'; then
  echo "AxLibQ2: ${c2}s of CPU for two queries, ${c1}s for one, ${c0}s for none"
  status=1
fi

# Many equal copies of one type that are separate objects. The walk without
# reuse costs one pass over each copy, so two queries over them must cost at
# most 1.5 times the file without queries, plus one second (a table that
# compares the copies of a bucket one by one costs the square of their number):
# - Coll20000: 20,000 axioms a(i) : forall x(i) : nat, nat, which differ only
#   in a binder name;
# - FunCopies: a functor with 100 parameters of one type, applied 200 times,
#   each application having its own copy of the type.
# And memory: a functor sealed by a module type gives its types as copies made
# anew in each query, so what the reuse keeps must not grow with the number of
# queries beyond what the entries need:
# - SealedFun: 800 axioms of one 800-wide type in a sealed functor, queried
#   in 13 groups and then as a whole; after the queries, the live heap (after
#   Optimize Heap) must be at most 1.25 times the live heap of the same file
#   without queries. The traversal without reuse is 1.207 times, the reuse
#   1.209 times, and keeping the types of every query 1.29 times (the file's
#   own modules are most of the heap).
coll() {
  for ((k = 1; k <= $1; k++)); do echo "Axiom a$k : forall x$k : nat, nat."; done
  for ((j = 0; j < $1; j += 100)); do
    echo "Definition c$((j / 100)) : nat := $(seq -f 'a%g 0' $((j + 1)) $((j + 100)) | paste -sd+ | sed 's/+/ + /g')."
  done
  echo "Definition R : nat := $(seq -f 'c%g' 0 $(($1 / 100 - 1)) | paste -sd+ | sed 's/+/ + /g')."
  for _ in 1 2; do echo "Print Assumptions R."; done
}

funcopies() {
  echo "Module Type T. Parameter t : Type. End T."
  echo "Module M <: T. Definition t := nat. End M."
  echo "Module F (X : T)."
  echo "  Parameters $(names 'a%g' $2): X.t."
  echo "  Definition u : list X.t := $(seq -f 'cons a%g (' 1 $2 | tr '\n' ' ')nil$(printf ')%.0s' $(seq 1 $2))."
  echo "End F."
  seq -f 'Module P%g := F M.' 1 $1
  echo "Definition R : list (list M.t) := $(seq -f 'cons P%g.u (' 1 $1 | tr '\n' ' ')nil$(printf ')%.0s' $(seq 1 $1))."
  for _ in 1 2; do echo "Print Assumptions R."; done
}

# 800 axioms of an 800-wide type in a functor F sealed by T, applied to M, and
# a root over groups of 64 of them; [$1] = queries asks for the group roots
# in turn, then the whole.
sealedfun() {
  local n=$2 groups=() g lo hi leaves k
  echo "Axiom G : $(yes 'nat ->' | head -n $n | tr '\n' ' ')Prop."
  echo "Module Type S."
  seq -f '  Parameter b%g : nat.' 1 $n
  echo "End S."
  echo "Module M <: S."
  seq -f '  Axiom b%g : nat.' 1 $n
  echo "End M."
  echo "Module Type T."
  echo "  Parameter W : Prop."
  seq -f '  Parameter a%g : W.' 1 $n
  echo "End T."
  echo "Module F (X : S) : T."
  echo "  Definition W : Prop := G $(seq -f 'X.b%g' 1 $n | tr '\n' ' ')."
  seq -f "  Axiom a%g : G $(seq -f 'X.b%g' 1 $n | tr '\n' ' ')." 1 $n
  echo "End F."
  echo "Module P := F M."
  echo "Definition f (x y : P.W) : P.W := x."
  for ((lo = 1; lo <= n; lo += 64)); do
    hi=$((lo + 63)); ((hi > n)) && hi=$n
    leaves=()
    for ((k = lo; k <= hi; k++)); do leaves+=("P.a$k"); done
    echo "Definition r$lo := $(tree "${leaves[@]}")."
    groups+=("r$lo")
  done
  echo "Definition R := $(tree "${groups[@]}")."
  if [ "$1" = queries ]; then
    for g in "${groups[@]}"; do echo "Print Assumptions $g."; done
    echo "Print Assumptions R."
  fi
  echo "Optimize Heap."
  echo "Print Debug GC."
}

coll 20000 > Coll20000.v
funcopies 200 100 > FunCopies.v
sealedfun queries 800 > SealedFunQ.v
sealedfun none 800 > SealedFun0.v
for f in Coll20000 FunCopies; do
  grep -v '^Print Assumptions' "$f.v" > "${f}NoQuery.v"
  full=$(cpu "$f.v")
  base=$(cpu "${f}NoQuery.v")
  expect "${f}NoQuery" "$(cat "${f}NoQuery.v.log")" ""
  # Both queries print the same lines: one header and one line per axiom each.
  expect "$f" "$(wc -l < "$f.v.log")" 40002
  expect "$f" "$(head -n 20001 "$f.v.log")" "$(tail -n 20001 "$f.v.log")"
  if ! awk -v f="$full" -v b="$base" 'BEGIN { exit !(f <= 1.5 * b + 1) }'; then
    echo "$f: ${full}s of CPU, against ${base}s without its queries"
    status=1
  fi
done

live() { awk '/^live_words:/ { gsub(/[.]/, "", $2); print $2 }' "$1"; }
rocq c -q -R . P SealedFunQ.v > SealedFunQ.v.log 2>&1 || true
rocq c -q -R . P SealedFun0.v > SealedFun0.v.log 2>&1 || true
lq=$(live SealedFunQ.v.log); l0=$(live SealedFun0.v.log)
expect SealedFunQ "$(grep -c '^Axioms:$' SealedFunQ.v.log)" 14
if ! awk -v q="$lq" -v z="$l0" 'BEGIN { exit !(z > 0 && q <= 1.25 * z) }'; then
  echo "SealedFunQ: ${lq} live words after its queries, against ${l0} without"
  status=1
fi
exit $status
