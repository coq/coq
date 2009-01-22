#! /bin/sh

dest=$1
shift

for f; do
  bn=`basename $f`
  dn=`dirname $f`
  install -d $dest/$dn
  install -m 644 $f $dest/$dn/$bn
done


