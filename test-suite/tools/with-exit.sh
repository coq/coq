#!/bin/sh
"$@"
status=$?
echo "exit status: $status"
exit $status
