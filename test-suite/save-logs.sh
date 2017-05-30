#!/usr/bin/env bash

WHERE="logs"

rsync -a --from0 --files-from=<(find . -name '*.log' -print0) . "$WHERE"
