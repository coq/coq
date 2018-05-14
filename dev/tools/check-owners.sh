#!/usr/bin/env bash

# Determine CODEOWNERS of the files given in argument
# For a given commit range:
# git diff --name-only -z COMMIT1 COMMIT2 | xargs -0 dev/tools/check-owners.sh [opts]

# NB: gitignore files will be messed up if you interrupt the script.
# You should be able to just move the .gitignore.bak files back manually.

usage() {
    { echo "usage: $0 [--show-patterns] [--owner OWNER] [FILE]..."
      echo "  --show-patterns: instead of printing file names print the matching patterns (more compact)"
      echo "  --owner: show only files/patterns owned by OWNER (use Nobody to see only non-owned files)"
    } >&2
}

case "$1" in
    "--help"|"-h")
        usage
        if [ $# = 1 ]; then exit 0; else exit 1; fi
esac

if ! [ -e .github/CODEOWNERS ]; then
    >&2 echo "No CODEOWNERS set up or calling from wrong directory."
    exit 1
fi

files=()
show_patterns=false

target_owner=""

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        "--show-patterns")
            show_patterns=true
            shift;;
        "--owner")
            if [[ "$#" = 1 ]]; then
                >&2 echo "Missing argument to --owner"
                usage
                exit 1
            elif [[ "$target_owner" != "" ]]; then
                >&2 echo "Only one --owner allowed"
                usage
                exit 1
            fi
            target_owner="$2"
            shift 2;;
        *)
            files+=("$@")
            break;;
    esac
done

# CODEOWNERS uses .gitignore patterns so we want to use git to parse it
# The only available tool for that is git check-ignore
# However it provides no way to use alternate .gitignore files
# so we rename them temporarily

find . -name .gitignore -print0 | while IFS= read -r -d '' f; do
    if [ -e "$f.bak" ]; then
        >&2 echo "$f.bak exists!"
        exit 1
    else
        mv "$f" "$f.bak"
    fi
done

# CODEOWNERS is not quite .gitignore patterns:
# after the pattern is the owner (space separated)
# git would interpret that as a big pattern containing spaces
# so we create a valid .gitignore by removing all but the first field

while read -r pat _; do
    printf '%s\n' "$pat" >> .gitignore
done < .github/CODEOWNERS

# associative array [file => owner]
declare -A owners

for f in "${files[@]}"; do
    data=$(git check-ignore --verbose --no-index "./$f")
    code=$?

    if [[ "$code" = 1 ]] || ! [[ "$data" =~ .gitignore:.* ]] ; then
        # no match, or match from non tracked gitignore (eg global gitignore)
        if [ "$target_owner" != "" ] && [ "$target_owner" != Nobody ] ; then
            owner=""
        else
            owner="Nobody"
            pat="$f" # no patterns for unowned files
        fi
    else
        # data looks like [.gitignore:$line:$pattern $file]
        # extract the line to look it up in CODEOWNERS
        data=${data#'.gitignore:'}
        line=${data%%:*}

        # NB: supports multiple owners
        # Does not support secondary owners declared in comment
        read -r pat fowners < <(sed "${line}q;d" .github/CODEOWNERS)

        owner=""
        if [ "$target_owner" != "" ]; then
            for o in $fowners; do # do not quote: multiple owners possible
                if [ "$o" = "$target_owner" ]; then
                    owner="$o"
                fi
            done
        else
            owner="$fowners"
        fi
    fi

    if [ "$owner" != "" ]; then
        if $show_patterns; then
            owners[$pat]="$owner"
        else
            owners[$f]="$owner"
        fi
    fi
done

for f in "${!owners[@]}"; do
    printf '%s: %s\n' "$f" "${owners[$f]}"
done | sort -k 2 -k 1 # group by owner

# restore gitignore files
rm .gitignore
find . -name .gitignore.bak -print0 | while IFS= read -r -d '' f; do
    base=${f%.bak}
    if [ -e "$base" ]; then
        >&2 echo "$base exists!"
    else
        mv "$f" "$base"
    fi
done
