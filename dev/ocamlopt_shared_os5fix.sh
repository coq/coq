#/bin/sh

### Temporary fix for production of .cmxs on MacOS 10.5

OCAMLOPT=$1
CMXS=$2

DIR=`dirname $CMXS`
BASE=`basename $CMXS .cmxs`
CMXA=$DIR/$BASE.cmxa
ARC=$DIR/$BASE.a
# we assume that all object files are at the same place than the rest
OBJS=`ar t $ARC | sed -e "s|^|$DIR/|" | grep -v SYMDEF`

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
# Build fixed .cmxs (assume all object files are at the same place)
ld -bundle -flat_namespace -undefined warning -read_only_relocs suppress -o $CMXS $OBJS $CMXS.startup.o
rm $CMXS.startup.o $CMXS.startup.s $CMXS.startup.fixed.s