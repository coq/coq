#!/usr/bin/env bash

# Determine CODEOWNERS of the files given in argument
# For a given commit range:
# git diff --name-only -z COMMIT1 COMMIT2 | xargs -0 dev/tools/check-owners.sh

# NB: gitignore files will be messed up if you interrupt the script.
# You should be able to just move the .gitignore.bak files back manually.

if [ $# = 0 ]; then
    >&2 echo "usage: $0 [FILE]..."
    exit 1
fi

if ! [ -e .github/CODEOWNERS ]; then
    >&2 echo "No CODEOWNERS set up or calling from wrong directory."
    exit 1
fi

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
    printf "%s\n" "$pat" >> .gitignore
done < .github/CODEOWNERS

# associative array [file => owner]
declare -A owners

for f in "$@"; do
    data=$(git check-ignore --verbose --no-index "./$f")
    code=$?

    if [[ "$code" = 1 ]] || ! [[ "$data" =~ .gitignore:.* ]] ; then
        # no match, or match from non tracked gitignore (eg global gitignore)
        owners[$f]="Nobody"
    else
        # data looks like [.gitignore:$line:$pattern $file]
        # extract the line to look it up in CODEOWNERS
        data=${data#'.gitignore:'}
        data=${data%%:*}

        # NB: supports multiple owners
        # Does not support secondary owners declared in comment
        read -r _ fowners < <(sed "${data}q;d" .github/CODEOWNERS)
        owners["$f"]="$fowners"
    fi
done

for f in "${!owners[@]}"; do
    printf "%s: %s\n" "$f" "${owners[$f]}"
done | sort -k 2 -k 1 # group by owner

# restort gitignore files
rm .gitignore
find . -name .gitignore.bak -print0 | while IFS= read -r -d '' f; do
    base=${f%.bak}
    if [ -e "$base" ]; then
        >&2 echo "$base exists!"
    else
        mv "$f" "$base"
    fi
done
