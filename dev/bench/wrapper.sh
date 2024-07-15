#!/bin/sh

log_dir=$COQ_LOG_DIR
runner=$COQ_RUNNER
package=$COQ_OPAM_PACKAGE
iteration=$COQ_ITERATION

echo "wrap[$package.$runner.$iteration|$OPAM_PACKAGE_NAME]" "$@" >> "$log_dir/wraplog.txt"
echo >> "$log_dir/wraplog.txt"

# we could be running commands for a dependency
# NB $package may contain the version
if [ "$package" ] && [ "$OPAM_PACKAGE_NAME" = "${package%%.*}" ] ; then
    prefix=$log_dir/$package.$runner.$iteration
    if [ -e "$prefix.ncoms" ]; then
        ncoms=$(cat "$prefix.ncoms")
        ncoms=$((ncoms+1))
    else
        ncoms=1
    fi
    echo $ncoms > "$prefix.ncoms"
    exec /usr/bin/time \
         -o "$prefix.$ncoms.time" --format="%U %M %F" \
         perf stat -e instructions:u,cycles:u -o "$prefix.$ncoms.perf" \
         "$@"
else
    exec "$@"
fi
