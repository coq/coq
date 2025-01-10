#!/usr/bin/env bash

set -ex

rocq=$(command -v rocq)
rocqhash=$(dune exec --root . -- dev/tools/hash.exe "$rocq")

rm -rf .wrappers
mkdir .wrappers

cat > .wrappers/coqc <<EOF
#!/bin/sh
# hash = $rocqhash
exec rocq c "\$@"
EOF

cat > .wrappers/coqdep <<EOF
#!/bin/sh
# hash = $rocqhash
exec rocq dep "\$@"
EOF

chmod +x .wrappers/coqc .wrappers/coqdep

ln -s "$(ocamlfind query rocq-runtime.kernel)" .wrappers/kernel

# fake coq-core.kernel for dune (mode native)
cat > .wrappers/META.coq-core <<EOF
package "kernel" (
  directory = "kernel"
  version = "dev"
  description = "The Coq Kernel"
  requires = "dynlink rocq-runtime.boot rocq-runtime.lib rocq-runtime.vm"
  archive(byte) = "kernel.cma"
  archive(native) = "kernel.cmxa"
  plugin(byte) = "kernel.cma"
  plugin(native) = "kernel.cmxs"
)
EOF

export PATH="$PWD/.wrappers:$PATH"
export OCAMLPATH="$PWD/.wrappers:$OCAMLPATH"

"$@"
