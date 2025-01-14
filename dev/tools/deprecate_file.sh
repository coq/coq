#!/bin/sh
usage()
{
        cat 1>&2 <<EOF
Usage: $0 FILE VERSION NOTE

        Write deprecation attributes in a Rocq source file for all commands that
        support it.
        Example: $0 Heap.v 8.3 "Use mergesort.v"
EOF
}

case $# in
        3) ;;
        *) usage; exit 1
esac

file=$1
vers=$2
note=$3

if ! [ -f "$file" ]; then
        printf '%s: %s: No such file\n' "$0" "$file" 1>&2
        exit 1
fi

attr="((Local|Global|Program|Canonical)[[:space:]]+)"

deprable="Theorem|Lemma|Fact|Corollary|Proposition|Property|\
Definition|Example|Fixpoint|\
Instance|Axiom|Parameter|Notation|Coercion"

annot="#[deprecated(since=\"$vers\", note=\"$note\")]"

tmp="$file".depr

sed -E "s/(^[[:space:]]*)(($attr)*($deprable).*\$)/\\1$annot\\n\\1\\2/" \
        "$file" >"$tmp"
mv "$tmp" "$file"
