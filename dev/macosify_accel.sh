#!/usr/bin/sed -f
s/^;\{0,1\} *\(.*\)<Control>\(.*\)$/\1<Primary>\2/
s/^;\{0,1\} *\(.*\)<Alt>\(.*\)$/\1<Control>\2/
