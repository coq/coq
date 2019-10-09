command -v "${BIN}votour" || { echo "Missing votour"; exit 1; }

"${BIN}votour" prerequisite/ssr_mini_mathcomp.vo < /dev/null
