#! /bin/sh

dest="$1"
shift

for f; do
  bn=$(basename "$f")
  dn=$(dirname "$f")
  install -d "$dest/$dn"
  case $bn in
      *.cmxs|*.py) install -m 755 "$f" "$dest/$dn/$bn"
	      ;;
      *) install -m 644 "$f" "$dest/$dn/$bn"
	 ;;
  esac
done
