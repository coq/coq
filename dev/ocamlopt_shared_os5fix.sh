#/bin/sh

### Temporary fix for production of .cmxs on MacOS 10.5

OCAMLOPT=$1
CMXS=$2
CMXA=$3

$OCAMLOPT -dstartup -linkall -shared -o $CMXS $CMXA
# Fix1: add a dummy instruction before the caml generic functions
# Fix2: make all caml generic functions private
rm -f $CMXS $CMXS.startup.fixed.s
cat $CMXS.startup.s | sed \
 -e "s/_caml_shared_startup__code_begin:/_caml_shared_startup__code_begin:	ret/" \
 -e "s/.globl	_caml_curry/.private_extern	_caml_curry/" \
 -e "s/.globl	_caml_apply/.private_extern	_caml_apply/" \
 -e "s/.globl	_caml_tuplify/.private_extern	_caml_tuplify/" \
 > $CMXS.startup.fixed.s
# Recompile fixed startup code
as -o $CMXS.startup.o $CMXS.startup.fixed.s
# Build fixed .cmxs (assume plugins are on directory base and include all files)
ld -bundle -flat_namespace -undefined warning -read_only_relocs suppress -o $CMXS `dirname $CMXS`/*.o
rm $CMXS.startup.o $CMXS.startup.s $CMXS.startup.fixed.s