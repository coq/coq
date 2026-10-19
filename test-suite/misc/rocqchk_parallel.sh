#!/usr/bin/env bash
# rocqchk -j N checks opaque proofs in forked worker processes. It must accept
# the same libraries as rocqchk -j 1, and reject a library as soon as one of
# its opaque proofs is ill-typed, whichever process checks it.
#
# The ill-typed proof is made by splicing: two compilations that differ only
# in one lemma have opaque tables with the same layout, so the library segment
# of the first one (where the lemma has type U) together with the opaques
# segment of the second one (where its proof has type U -> U) makes a well
# formed .vo whose proof of that lemma does not have the type it claims.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
mkdir "$d/good" "$d/bad" "$d/late"

# Many opaque proofs, so that there is work for several workers. The bad
# library has its ill-typed proof first. The late one has it at l9: the queue
# is dealt in a stride of 2 x N, so l9 is the second proof of the first
# worker's first batch at -j 4 and its third at -j 2, and with
# -worker-budget 0 that worker stops after l1. l9 is then checked only from
# the proofs the worker gives back.
gen() {
  echo 'Inductive T : Prop := I.'
  echo 'Definition U := T.'
  for i in $(seq 1 400); do
    if { [ "$i" = 1 ] && [ "$1" = bad ]; } || { [ "$i" = 9 ] && [ "$1" = late ]; }; then
      echo "Lemma l$i : forall x : U, U. Proof. exact (fun x => x). Qed."
    else
      echo "Lemma l$i : U. Proof. exact I. Qed."
    fi
    echo "Definition d$i := l$i."
  done
}
gen good > "$d/good/Lib.v"
gen bad > "$d/bad/Lib.v"
gen late > "$d/late/Lib.v"
rocq c -native-compiler no -R "$d/good" "" "$d/good/Lib.v"
rocq c -native-compiler no -R "$d/bad" "" "$d/bad/Lib.v"
rocq c -native-compiler no -R "$d/late" "" "$d/late/Lib.v"

python3 - "$d" <<'PY'
import os, sys, hashlib, struct
d = sys.argv[1]
MAGIC = 0x436F7121  # "Coq!"; all ints big-endian, layout per lib/objFile.ml
def parse(p):
    b = open(p, "rb").read()
    magic, ver = struct.unpack_from(">II", b, 0)
    assert magic == MAGIC, "bad magic"
    (sp,) = struct.unpack_from(">Q", b, 8)
    off = sp
    (n,) = struct.unpack_from(">I", b, off); off += 4
    segs = {}
    for _ in range(n):
        (nl,) = struct.unpack_from(">I", b, off); off += 4
        name = b[off:off+nl].decode(); off += nl
        pos, ln = struct.unpack_from(">QQ", b, off); off += 16
        h = b[off:off+16]; off += 16
        data = b[pos:pos+ln]
        assert hashlib.md5(data).digest() == h, name + ": bad segment MD5"
        segs[name] = data
    return ver, segs
def write(p, ver, by):
    out = bytearray()
    out += struct.pack(">II", MAGIC, ver)
    out += struct.pack(">Q", 0)              # summary position placeholder
    summ = []
    for name in sorted(by):                  # CString.Map.iter order
        data = by[name]; pos = len(out); out += data
        h = hashlib.md5(data).digest(); out += h
        summ.append((name, pos, len(data), h))
    sp = len(out)
    out += struct.pack(">I", len(summ))
    for name, pos, ln, h in summ:
        nb = name.encode()
        out += struct.pack(">I", len(nb)); out += nb
        out += struct.pack(">QQ", pos, ln); out += h
    struct.pack_into(">Q", out, 8, sp)
    open(p, "wb").write(out)
vg, sg = parse(d + "/good/Lib.vo")
for bad, out in (("bad", d + "/Lib.vo"), ("late", d + "/late-spliced/Lib.vo")):
    vb, sb = parse(d + "/" + bad + "/Lib.vo")
    assert vg == vb, "vo_version mismatch"
    assert sg["opaques"] != sb["opaques"], "opaques should differ"
    spliced = dict(sg)
    spliced["opaques"] = sb["opaques"]
    os.makedirs(os.path.dirname(out), exist_ok=True)
    write(out, vg, spliced)
PY

# Expected output in misc/rocqchk_parallel.out. The error of the bad library
# is found in the first opaque proof, which always goes to the first worker, so
# the output is deterministic except for the worker's process id.
run() {
  echo "== $1"
  shift
  R=0
  rocqchk -silent "$@" > "$d/run.log" 2>&1 || R=$?
  sed -e 's/Worker process [0-9]*/Worker process PID/' "$d/run.log"
  echo "exit code: $R"
}
# The late refusal is found by a worker, but which batch l9 is in once it has
# been given back depends on timing, so the batch is not kept.
run_late() {
  echo "== $1"
  shift
  R=0
  rocqchk -silent "$@" > "$d/run.log" 2>&1 || R=$?
  grep -q 'Type error: ActualType' "$d/run.log" && echo "type error reported"
  grep -q 'while checking the opaque proof of Lib.l9\.' "$d/run.log" && echo "proof reported: Lib.l9"
  echo "exit code: $R"
}
{
  for j in 1 2 4; do run "correct library, -j $j" -j $j -R "$d/good" "" -norec Lib; done
  for j in 1 2 4; do run "ill-typed proof, -j $j" -j $j -R "$d" "" -norec Lib; done
  # A worker that stops after each check gives its other proofs back: the
  # verdict is the same.
  run "correct library, -j 4, -worker-budget 0" -j 4 -worker-budget 0 -R "$d/good" "" -norec Lib
  run "ill-typed proof, -j 4, -worker-budget 0" -j 4 -worker-budget 0 -R "$d" "" -norec Lib
  # The refusing proof is in the first batch but is not its first proof: it is
  # checked only after that batch's worker gives it back.
  run_late "ill-typed late proof, -j 4, -worker-budget 0" -j 4 -worker-budget 0 -R "$d/late-spliced" "" -norec Lib
  run_late "ill-typed late proof, -j 2, -worker-budget 0" -j 2 -worker-budget 0 -R "$d/late-spliced" "" -norec Lib
  # Profiling is sequential only.
  run "-j 2 with -profile" -j 2 -profile "$d/prof.json" -R "$d/good" "" -norec Lib
} > "$d/actual.out"

diff -u misc/rocqchk_parallel.out "$d/actual.out"
