#!/bin/bash
command -v "votour" || { echo "Missing votour"; exit 1; }

"votour" ../prerequisite/ssr_mini_mathcomp.vo
