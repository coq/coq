#!/bin/sh

set -e

for i in "$3/"*.dylib
do install_name_tool -change "$2"/$(basename $i) @executable_path/../Resources/lib/$(basename $i) "$1"
done
case "$1" in
	*.dylib)
	    install_name_tool -id @executable_path/../Resources/lib/$(basename $1) $1
	    for i in "$3"/*.dylib
	    do install_name_tool -change "$2/"$(basename $1) @executable_path/../Resources/lib/$(basename $1) $i
	    done;;
	*)
esac
