#!/usr/bin/env bash
# rocqchk with -bytecode-compiler yes used to take the VM bytecode of a constant
# from the vmlibrary segment of the .vo while typechecking its body from the
# library segment, with nothing tying the two together. A .vo whose vmlibrary
# disagrees with its library then let a VMcast prove False, and rocqchk accepted
# the result with no axioms reported.
#
# rocqchk now compiles the bytecode itself, from the bodies it checks, and never
# reads the vmlibrary segment at all. So:
#  - a .vo with a bogus vmlibrary is still accepted, because its declarations are
#    well typed and the bogus segment is simply ignored; but
#  - a library built against it, whose VMcast only typechecked because the
#    compiler believed the bogus bytecode, is rejected with a plain type error.
#
# No patched tool is needed to build the bogus .vo: two honest compilations that
# differ only in one constant's value produce byte-identical opaques/summary
# segments, so splicing d1's library together with d2's vmlibrary yields an
# internally consistent file whose bytecode no longer matches its body.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
mkdir "$d/d1" "$d/d2"

# poc_evil's body is (idb true) in d1 and (idb false) in d2; -noinit keeps the
# file self-contained so rocqchk has nothing else to load.
cat > "$d/d1/Defs.v" <<'EOF'
Unset Elimination Schemes.
Inductive bool : Set := true | false.
Definition idb (b : bool) : bool := b.
Definition poc_evil : bool := idb true.
EOF
sed 's/idb true/idb false/' "$d/d1/Defs.v" > "$d/d2/Defs.v"

# Native compilation is off throughout: splicing Defs.vo leaves the .coq-native
# files of the two builds behind, and compiling Evil against them fails to find
# the module they were emitted for. The bug under test is about VM bytecode.
rocq c -noinit -native-compiler no -R "$d/d1" "" "$d/d1/Defs.v"
rocq c -noinit -native-compiler no -R "$d/d2" "" "$d/d2/Defs.v"

# Splice: library from d1 (body says true), vmlibrary from d2 (bytecode says
# false), keeping d1's opaques/summary. All per-segment MD5s and the summary
# offsets are recomputed so the container is well formed.
python3 - "$d" <<'PY'
import sys, hashlib, struct
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
v1, s1 = parse(d + "/d1/Defs.vo")
v2, s2 = parse(d + "/d2/Defs.vo")
assert v1 == v2, "vo_version mismatch"
assert s1["library"]   != s2["library"],   "library should differ"
assert s1["vmlibrary"] != s2["vmlibrary"], "vmlibrary should differ"
write(d + "/Defs.vo", v1, {"library":   s1["library"],
                           "vmlibrary": s2["vmlibrary"],
                           "opaques":   s1["opaques"],
                           "summary":   s1["summary"]})
PY

# The spliced file is well typed, only its bytecode lies, and rocqchk no longer
# looks at that; accepting it is the point of the design.
if ! rocqchk -bytecode-compiler yes -R "$d" "" Defs 2> "$d/err0"; then
  >&2 echo "FAILURE: rocqchk rejected a well-typed .vo because of its vmlibrary segment"
  cat "$d/err0" >&2
  exit 1
fi

# poc_evil is (idb true), i.e. true, so [discr poc_evil] is [False]. The spliced
# vmlibrary makes the compiler's VM believe it is [false], i.e. [True], so the
# VMcast below goes through and Evil.vo holds a proof of False.
cat > "$d/Evil.v" <<'EOF'
Require Import Defs.
Inductive False : Prop := .
Inductive True : Prop := I.
Definition discr (b : bool) : Prop := match b with true => False | false => True end.
Definition oops : discr poc_evil := (I <: discr poc_evil).
Definition boom : False := oops.
EOF
rocq c -noinit -native-compiler no -bytecode-compiler yes -R "$d" "" "$d/Evil.v"

# rocqchk computes with its own bytecode, so the VMcast simply fails to convert
# and Evil is rejected with the same type error the default checker gives.
if rocqchk -bytecode-compiler yes -R "$d" "" Evil 2> "$d/err"; then
  >&2 echo "FAILURE: rocqchk accepted a proof of False built on a bogus vmlibrary"
  cat "$d/err" >&2
  exit 1
fi
grep -q "Type error" "$d/err" || { >&2 echo "FAILURE: rejected, but not as a type error"; cat "$d/err" >&2; exit 1; }
exit 0
