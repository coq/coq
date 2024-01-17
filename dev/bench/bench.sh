#! /usr/bin/env bash

# ASSUMPTIONS:
# - the OPAM packages, specified by the user, are topologically sorted wrt. to the dependency relationship.
# - all the variables below are set.

set -e

BENCH_DEBUG=

r='\033[0m'          # reset (all attributes off)
b='\033[1m'          # bold
u='\033[4m'          # underline
nl=$'\n'
bt='`'               # backtick
start_code_block='```'
end_code_block='```'

# We put local binaries such as opam in .bin and extend PATH
BIN=$(pwd)/.bin
mkdir "$BIN"
wget https://github.com/ocaml/opam/releases/download/2.1.3/opam-2.1.3-x86_64-linux -O "$BIN"/opam
chmod +x "$BIN"/opam

export NJOBS=1 # used by the test suite through dune

# generate per file info in test suite and coq_makefile devs
export TIMED=1

export PATH="$BIN":$PATH

echo "Global env info:"
echo "----------------"
echo "pwd: $PWD"
echo "path: $PATH"
echo "opam version: `opam --version`"

number_of_processors=$(cat /proc/cpuinfo | grep '^processor *' | wc -l)

program_name="$0"
program_path=$(readlink -f "${program_name%/*}")
render_results="dune exec --no-print-directory --root $program_path/../.. -- dev/bench/render_results.exe"
render_line_results="dune exec --no-print-directory --root $program_path/../.. -- dev/bench/render_line_results.exe"
timelog2html="dune exec --no-print-directory --root $program_path/../.. -- dev/bench/timelog2html.exe"

coqbot_url_prefix="https://coqbot.herokuapp.com/pendulum/"

# Check that the required arguments are provided

check_variable () {
  if [ ! -v "$1" ]
  then
      echo "Variable $1 should be set"
      exit 1
  fi
}

#check_variable "BUILD_ID"
#check_variable "BUILD_URL"
#check_variable "JOB_NAME"
#check_variable "JENKINS_URL"
#check_variable "CI_JOB_URL"
#check_variable "CI_REPOSITORY_URL"

: "${coq_pr_number:=}"
: "${coq_pr_comment_id:=}"
: "${new_ocaml_version:=4.14.1}"
: "${old_ocaml_version:=4.14.1}"
: "${new_ocaml_flambda:=0}"
: "${old_ocaml_flambda:=0}"
: "${new_coq_repository:=$CI_REPOSITORY_URL}"
: "${old_coq_repository:=$CI_REPOSITORY_URL}"
: "${new_coq_opam_archive_git_uri:=https://github.com/coq/opam-coq-archive.git}"
: "${old_coq_opam_archive_git_uri:=https://github.com/coq/opam-coq-archive.git}"
: "${new_coq_opam_archive_git_branch:=master}"
: "${old_coq_opam_archive_git_branch:=master}"
: "${new_coq_version:=dev}"
: "${old_coq_version:=dev}"
: "${num_of_iterations:=1}"
: "${timeout:=3h}"
: "${coq_opam_packages:=coq-bignums coq-hott coq-performance-tests-lite coq-engine-bench-lite coq-mathcomp-ssreflect coq-mathcomp-fingroup coq-mathcomp-algebra coq-mathcomp-solvable coq-mathcomp-field coq-mathcomp-character coq-mathcomp-odd-order coq-math-classes coq-corn coq-compcert coq-equations coq-metacoq-template coq-metacoq-pcuic coq-metacoq-safechecker coq-metacoq-erasure coq-metacoq-translations coq-color coq-coqprime coq-coqutil coq-bedrock2 coq-rewriter coq-fiat-core coq-fiat-parsers coq-fiat-crypto-with-bedrock coq-unimath coq-coquelicot coq-iris-examples coq-verdi coq-verdi-raft coq-fourcolor coq-rewriter-perf-SuperFast coq-vst coq-category-theory coq-neural-net-interp-computed-lite}"
: "${coq_native:=}"
: "${skip_coq_tests:=}"

: "${new_coq_commit:=$(git rev-parse HEAD^2)}"
: "${old_coq_commit:=$(git merge-base HEAD^1 $new_coq_commit)}"

new_ocaml_switch=ocaml-base-compiler.$new_ocaml_version
old_ocaml_switch=ocaml-base-compiler.$old_ocaml_version

if echo "$num_of_iterations" | grep '^[1-9][0-9]*$' 2> /dev/null > /dev/null; then
    :
else
    echo
    echo "ERROR: num_of_iterations \"$num_of_iterations\" is not a positive integer." > /dev/stderr
    print_man_page_hint
    exit 1
fi

bench_dirname="_bench"
mkdir -p "${bench_dirname}"
working_dir="$PWD/${bench_dirname}"

log_dir=$working_dir/logs
mkdir "$log_dir"
export COQ_LOG_DIR=$log_dir

echo "DEBUG: ocaml -version = $(ocaml -version)"
echo "DEBUG: working_dir = $working_dir"
echo "DEBUG: new_ocaml_switch = $new_ocaml_switch"
echo "DEBUG: new_coq_repository = $new_coq_repository"
echo "DEBUG: new_coq_commit = $new_coq_commit"
echo "DEBUG: new_coq_opam_archive_git_uri = $new_coq_opam_archive_git_uri"
echo "DEBUG: new_coq_opam_archive_git_branch = $new_coq_opam_archive_git_branch"
echo "DEBUG: old_ocaml_switch = $old_ocaml_switch"
echo "DEBUG: old_coq_repository = $old_coq_repository"
echo "DEBUG: old_coq_commit = $old_coq_commit"
echo "DEBUG: old_coq_opam_archive_git_uri = $old_coq_opam_archive_git_uri"
echo "DEBUG: old_coq_opam_archive_git_branch = $old_coq_opam_archive_git_branch"
echo "DEBUG: num_of_iterations = $num_of_iterations"
echo "DEBUG: coq_opam_packages = $coq_opam_packages"
echo "DEBUG: coq_pr_number = $coq_pr_number"
echo "DEBUG: coq_pr_comment_id = $coq_pr_comment_id"
echo "DEBUG: coq_native = $coq_native"

# --------------------------------------------------------------------------------

# Some sanity checks of command-line arguments provided by the user that can be done right now.

if which perf > /dev/null; then
    echo -n
else
    echo > /dev/stderr
    echo "ERROR: \"perf\" program is not available." > /dev/stderr
    echo > /dev/stderr
    exit 1
fi

if which curl > /dev/null; then
    :
else
    echo > /dev/stderr
    echo "ERROR: \"curl\" program is not available." > /dev/stderr
    echo > /dev/stderr
    exit 1
fi

if which du > /dev/null; then
    :
else
    echo > /dev/stderr
    echo "ERROR: \"du\" program is not available." > /dev/stderr
    echo > /dev/stderr
    exit 1
fi

if [ ! -e "$working_dir" ]; then
    echo > /dev/stderr
    echo "ERROR: \"$working_dir\" does not exist." > /dev/stderr
    echo > /dev/stderr
    exit 1
fi

if [ ! -d "$working_dir" ]; then
    echo > /dev/stderr
    echo "ERROR: \"$working_dir\" is not a directory." > /dev/stderr
    echo > /dev/stderr
    exit 1
fi

if [ ! -w "$working_dir" ]; then
    echo > /dev/stderr
    echo "ERROR: \"$working_dir\" is not writable." > /dev/stderr
    echo > /dev/stderr
    exit 1
fi

coq_opam_packages_on_separate_lines=$(echo "$coq_opam_packages" | sed 's/ /\n/g')
if [ $(echo "$coq_opam_packages_on_separate_lines" | wc -l) != $(echo "$coq_opam_packages_on_separate_lines" | sort | uniq | wc -l) ]; then
    echo "ERROR: The provided set of OPAM packages contains duplicates."
    exit 1
fi

# --------------------------------------------------------------------------------

# Tell coqbot to update the initial comment, if we know which one to update
function coqbot_update_comment() {
    is_done="$1"
    comment_body="$2"
    uninstallable_packages="$3"

    if [ ! -z "${coq_pr_number}" ]; then
        comment_text=""
        artifact_text=""

        if [ -z "${is_done}" ]; then
            comment_text="in progress, "
            artifact_text="eventually "
        else
            comment_text=""
            artifact_text=""
        fi
        comment_text="Benchmarking ${comment_text}log available [here](${CI_JOB_URL}) ([raw log here](${CI_JOB_URL}/raw)), artifacts ${artifact_text}available for [download](${CI_JOB_URL}/artifacts/download) and [browsing](${CI_JOB_URL}/artifacts/browse)"

        if [ ! -z "${comment_body}" ]; then
            comment_text="${comment_text}${nl}${start_code_block}${nl}${comment_body}${nl}${end_code_block}"
        fi

        if [ ! -z "${uninstallable_packages}" ]; then
            comment_text="${comment_text}${nl}The following packages failed to install: ${uninstallable_packages}"
        fi

        comment_text="${comment_text}${nl}${nl}<details><summary>Old Coq version ${old_coq_commit}</summary>"
        comment_text="${comment_text}${nl}${nl}${start_code_block}${nl}$(git log -n 1 "${old_coq_commit}")${nl}${end_code_block}${nl}</details>"
        comment_text="${comment_text}${nl}${nl}<details><summary>New Coq version ${new_coq_commit}</summary>"
        comment_text="${comment_text}${nl}${nl}${start_code_block}${nl}$(git log -n 1 "${new_coq_commit}")${nl}${end_code_block}${nl}</details>"
        comment_text="${comment_text}${nl}${nl}[Diff: ${bt}${old_coq_commit}..${new_coq_commit}${bt}](https://github.com/coq/coq/compare/${old_coq_commit}..${new_coq_commit})"

        # if there's a comment id, we update the comment while we're
        # in progress; otherwise, we wait until the end to post a new
        # comment
        if [ ! -z "${coq_pr_comment_id}" ]; then
            # Tell coqbot to update the in-progress comment
            curl -X POST --data-binary "${coq_pr_number}${nl}${coq_pr_comment_id}${nl}${comment_text}" "${coqbot_url_prefix}/update-comment"
        elif [ ! -z "${is_done}" ]; then
            # Tell coqbot to post a new comment that we're done benchmarking
            curl -X POST --data-binary "${coq_pr_number}${nl}${comment_text}" "${coqbot_url_prefix}/new-comment"
        fi
        if [ ! -z "${is_done}" ]; then
            # Tell coqbot to remove the `needs: benchmarking` label
            curl -X POST --data-binary "${coq_pr_number}" "${coqbot_url_prefix}/benchmarking-done"
        fi
    fi
}

# initial update to the comment, to say that we're in progress
coqbot_update_comment "" "" ""

# --------------------------------------------------------------------------------

zulip_post=""
if [[ $ZULIP_BENCH_BOT ]]; then
    pr_full=$(git log -n 1 --pretty=%s)
    pr_full=${pr_full#"[CI merge] PR #"}
    pr_num=${pr_full%%:*}
    pr_msg=${pr_full#*:}
    zulip_header="Bench at $CI_JOB_URL
Testing [$pr_msg](https://github.com/coq/coq/pull/$pr_num)
On packages $coq_opam_packages
"

    # 24008 is the "github notifications" stream
    resp=$(curl -sSX POST https://coq.zulipchat.com/api/v1/messages \
    -u "$ZULIP_BENCH_BOT" \
    --data-urlencode type=stream \
    --data-urlencode to='240008' \
    --data-urlencode subject='Bench Notifications' \
    --data-urlencode content="$zulip_header")

    zulip_post=$(echo "$resp" | jq .id)
    case "$zulip_post" in
        ''|*[!0-9]*) # not an int
            echo "Failed to post to zulip: $resp"
            zulip_post=""
            ;;
    esac
fi

zulip_edit() {
    if ! [[ $zulip_post ]]; then return; fi
    ending=$1
    if [[ $rendered_results ]]; then
        msg="$zulip_header

~~~
$rendered_results
~~~

$ending
"
    else
        msg="$zulip_header

$ending
"
    fi
    curl -sSX PATCH https://coq.zulipchat.com/api/v1/messages/"$zulip_post" \
         -u "$ZULIP_BENCH_BOT" \
         --data-urlencode content="$msg" >/dev/null || echo "Failed to edit zulip post" >&2
}
zulip_autofail() {
    code=$?
    com=$BASH_COMMAND
    zulip_edit "Failed '$com' with exit code $code."
}
if [[ $zulip_post ]]; then trap zulip_autofail ERR; fi

# see https://github.com/coq/coq/pull/15807
ulimit -S -s $((2 * $(ulimit -s)))

# Clone the indicated git-repository.

coq_dir="$working_dir/coq"
git clone -q "$new_coq_repository" "$coq_dir"
cd "$coq_dir"
git remote rename origin new_coq_repository
git remote add old_coq_repository "$old_coq_repository"
git fetch -q "$old_coq_repository"
git checkout -q $new_coq_commit

coq_opam_version=dev

# --------------------------------------------------------------------------------

new_opam_root="$working_dir/opam.NEW"
old_opam_root="$working_dir/opam.OLD"

# --------------------------------------------------------------------------------

old_coq_opam_archive_dir="$working_dir/old_coq_opam_archive"
git clone -q --depth 1 -b "$old_coq_opam_archive_git_branch" "$old_coq_opam_archive_git_uri" "$old_coq_opam_archive_dir"
new_coq_opam_archive_dir="$working_dir/new_coq_opam_archive"
git clone -q --depth 1 -b "$new_coq_opam_archive_git_branch" "$new_coq_opam_archive_git_uri" "$new_coq_opam_archive_dir"

initial_opam_packages="num ocamlfind dune"

# Create an opam root and install Coq
# $1 = root_name {ex: NEW / OLD}
# $2 = compiler name
# $3 = git hash of Coq to be installed
# $4 = directory of coq opam archive
# $5 = use flambda if nonempty
create_opam() {

    local RUNNER="$1"
    local OPAM_DIR="$working_dir/opam.$RUNNER"
    local OCAML_VER="$2"
    local COQ_HASH="$3"
    local COQ_VER="$4"
    local OPAM_COQ_DIR="$5"
    local USE_FLAMBDA="$6"

    local OPAM_COMP=ocaml-base-compiler.$OCAML_VER

    export OPAMROOT="$OPAM_DIR"
    export COQ_RUNNER="$RUNNER"

    opam init --disable-sandboxing -qn -j$number_of_processors --bare
    # Allow beta compiler switches
    opam repo add -q --set-default beta https://github.com/ocaml/ocaml-beta-repository.git
    # Allow experimental compiler switches
    opam repo add -q --set-default ocaml-pr https://github.com/ejgallego/ocaml-pr-repository.git
    # Rest of default switches
    opam repo add -q --set-default iris-dev "https://gitlab.mpi-sws.org/FP/opam-dev.git"

    if [[ $USE_FLAMBDA = 1 ]];
    then flambda=--packages=ocaml-variants.${OCAML_VER}+options,ocaml-option-flambda
    else flambda=
    fi

    opam switch create -qy -j$number_of_processors "ocaml-$RUNNER" "$OPAM_COMP" $flambda
    eval $(opam env)

    # For some reason opam guesses an incorrect upper bound on the
    # number of jobs available on Travis, so we set it here manually:
    opam var --global jobs=$number_of_processors >/dev/null
    if [ ! -z "$BENCH_DEBUG" ]; then opam config list; fi

    opam repo add -q --this-switch coq-extra-dev "$OPAM_COQ_DIR/extra-dev"
    opam repo add -q --this-switch coq-released "$OPAM_COQ_DIR/released"

    # Pinning for packages that are not in a repository
    opam pin add -ynq coq-perennial.dev git+https://github.com/mit-pdos/perennial#coq/tested

    opam install -qy -j$number_of_processors $initial_opam_packages
    if [ ! -z "$BENCH_DEBUG" ]; then opam repo list; fi

    cd "$coq_dir"
    echo "$1_coq_commit = $COQ_HASH"

    echo "wrap-build-commands: [\"$program_path/wrapper.sh\"]" >> "$OPAM_DIR/config"

    git checkout -q $COQ_HASH
    COQ_HASH_LONG=$(git log --pretty=%H | head -n 1)

    echo "$1_coq_commit_long = $COQ_HASH_LONG"

    if [ ! -z "$coq_native" ]; then opam install coq-native; fi

    for package in coq-core coq-stdlib coqide-server coq; do
        export COQ_OPAM_PACKAGE=$package
        export COQ_ITERATION=1

        # build stdlib with -j 1 to get nicer timings
        local this_nproc=$number_of_processors
        if [ "$package" = coq-stdlib ]; then this_nproc=1; fi

        with_test=--with-test
        if [ "$skip_coq_tests" ]; then with_test=; fi

        _RES=0
        opam pin add -y -b -j "$this_nproc" --kind=path $with_test $package.$COQ_VER . \
             3>$log_dir/$package.$RUNNER.opam_install.1.stdout.log 1>&3 \
             4>$log_dir/$package.$RUNNER.opam_install.1.stderr.log 2>&4 || \
            _RES=$?
        if [ $_RES = 0 ]; then
            echo "$package ($RUNNER) installed successfully"
        else
            echo "ERROR: \"opam install $package.$coq_opam_version\" has failed (for the $RUNNER commit = $COQ_HASH_LONG)."
            zulip_edit "Bench failed: could not install $package ($RUNNER)."
            exit 1
        fi

        # we don't multi compile coq for now (TODO some other time)
        # the render needs all the files so copy them around
        for it in $(seq 2 $num_of_iterations); do
            cp "$log_dir/$package.$RUNNER.1.time" "$log_dir/$package.$RUNNER.$it.time"
            cp "$log_dir/$package.$RUNNER.1.perf" "$log_dir/$package.$RUNNER.$it.perf"
        done
    done

}

# Create an OPAM-root to which we will install the NEW version of Coq.
create_opam "NEW" "$new_ocaml_version" "$new_coq_commit" "$new_coq_version" \
            "$new_coq_opam_archive_dir" "$new_ocaml_flambda"
new_coq_commit_long="$COQ_HASH_LONG"

# Create an OPAM-root to which we will install the OLD version of Coq.
create_opam "OLD" "$old_ocaml_version" "$old_coq_commit" "$old_coq_version" \
            "$old_coq_opam_archive_dir" "$old_ocaml_flambda"
old_coq_commit_long="$COQ_HASH_LONG"

# Packages which appear in the rendered table
# Deliberately don't include the "coqide-server" package
installable_coq_opam_packages="coq-core coq-stdlib coq"

echo "DEBUG: $render_results $log_dir $num_of_iterations $new_coq_commit_long $old_coq_commit_long 0 user_time_pdiff $installable_coq_opam_packages"
rendered_results="$($render_results "$log_dir" $num_of_iterations $new_coq_commit_long $old_coq_commit_long 0 user_time_pdiff $installable_coq_opam_packages)"
echo "${rendered_results}"
zulip_edit "Benching continues..."

# HTML for stdlib
# NB: unlike coq_makefile packages, stdlib produces foo.timing not foo.v.timing
new_base_path=$new_opam_root/ocaml-NEW/.opam-switch/build/coq-stdlib.dev/_build/default/theories/
old_base_path=$old_opam_root/ocaml-OLD/.opam-switch/build/coq-stdlib.dev/_build/default/theories/
for vo in $(cd $new_base_path/; find . -name '*.vo'); do
    if [ -e $old_base_path/$vo ]; then
        echo "$coq_opam_package/$vo $(stat -c%s $old_base_path/$vo) $(stat -c%s $new_base_path/$vo)" >> "$log_dir/vosize.log"
    fi
    if [ -e $old_base_path/${vo%%.vo}.timing ] && \
           [ -e $new_base_path/${vo%%.vo}.timing ]; then
        mkdir -p $working_dir/html/coq-stdlib/$(dirname $vo)/
        # NB: sometimes randomly fails
        $timelog2html $new_base_path/${vo%%o} \
                      $old_base_path/${vo%%.vo}.timing \
                      $new_base_path/${vo%%.vo}.timing > \
                      $working_dir/html/coq-stdlib/${vo%%o}.html ||
            echo "Failed (code $?):" $timelog2html $new_base_path/${vo%%o} \
                 $old_base_path/${vo%%.vo}.timing \
                 $new_base_path/${vo%%.vo}.timing
    fi
done

# --------------------------------------------------------------------------------
# Measure the compilation times of the specified OPAM packages in both switches

# Sort the opam packages
sorted_coq_opam_packages=$("${program_path}/sort-by-deps.sh" ${coq_opam_packages})
echo "sorted_coq_opam_packages = ${sorted_coq_opam_packages}"

failed_packages=
skipped_packages=

# Generate per line timing info in devs that use coq_makefile
export TIMING=1
export PROFILING=1
export COQ_PROFILE_COMPONENTS=command,parse_command

for coq_opam_package in $sorted_coq_opam_packages; do

    export COQ_OPAM_PACKAGE=$coq_opam_package
    if [ ! -z "$BENCH_DEBUG" ]; then
        opam list
        opam show $coq_opam_package || {
            failed_packages="$failed_packages
$coq_opam_package (unknown package)"
            continue
            }
    else
        # cause to skip with error if unknown package
        opam show $coq_opam_package >/dev/null || {
            failed_packages="$failed_packages
$coq_opam_package (unknown package)"
            continue
            }
    fi
    echo "coq_opam_package = $coq_opam_package"

    for RUNNER in NEW OLD; do

        export COQ_RUNNER=$RUNNER

        # perform measurements for the NEW/OLD commit (provided by the user)
        if [ $RUNNER = "NEW" ]; then
            export OPAMROOT="$new_opam_root"
            echo "Testing NEW commit: $(date)"
        else
            export OPAMROOT="$old_opam_root"
            echo "Testing OLD commit: $(date)"
        fi

        eval $(opam env)

        # If a given OPAM-package was already installed (as a
        # dependency of some OPAM-package that we have benchmarked
        # before), remove it.
        opam uninstall -q $coq_opam_package >/dev/null 2>&1

        for dep in $(opam install --show-actions "$coq_opam_package" | grep -o '∗\s*install\s*[^ ]*' | sed 's/∗\s*install\s*//g'); do
            # show-actions will print transitive deps
            # so we don't need to look at the skipped_packages
            if echo "$failed_packages" | grep -q "$dep"; then
                skipped_packages="$skipped_packages
$coq_opam_package (dependency $dep failed)"
                continue 3
            fi
        done

        # OPAM 2.0 likes to ignore the -j when it feels like :S so we
        # workaround that here.
        opam var --global jobs=$number_of_processors >/dev/null

        opam install $coq_opam_package -v -b -j$number_of_processors --deps-only -y \
             3>$log_dir/$coq_opam_package.$RUNNER.opam_install.deps_only.stdout.log 1>&3 \
             4>$log_dir/$coq_opam_package.$RUNNER.opam_install.deps_only.stderr.log 2>&4 || {
            failed_packages="$failed_packages
$coq_opam_package (dependency install failed in $RUNNER)"
            continue 2
            }

        opam var --global jobs=1 >/dev/null

        if [ ! -z "$BENCH_DEBUG" ]; then ls -l $working_dir; fi

        for iteration in $(seq $num_of_iterations); do
            export COQ_ITERATION=$iteration
            _RES=0
            timeout "$timeout" opam install -v -b -j1 $coq_opam_package \
                 3>$log_dir/$coq_opam_package.$RUNNER.opam_install.$iteration.stdout.log 1>&3 \
                 4>$log_dir/$coq_opam_package.$RUNNER.opam_install.$iteration.stderr.log 2>&4 || \
                _RES=$?
            if [ $_RES = 0 ];
            then
                echo $_RES > $log_dir/$coq_opam_package.$RUNNER.opam_install.$iteration.exit_status
                # "opam install" was successful.

                # Remove the benchmarked OPAM-package, unless this is the
                # very last iteration (we want to keep this OPAM-package
                # because other OPAM-packages we will benchmark later
                # might depend on it --- it would be a waste of time to
                # remove it now just to install it later)
                if [ $iteration != $num_of_iterations ]; then
                    opam uninstall -q $coq_opam_package
                fi
            else
                # "opam install" failed.
                echo $_RES > $log_dir/$coq_opam_package.$RUNNER.opam_install.$iteration.exit_status
                failed_packages="$failed_packages
$coq_opam_package"
                continue 3
            fi
        done
    done

    installable_coq_opam_packages="$installable_coq_opam_packages $coq_opam_package"

    # --------------------------------------------------------------
    cat $log_dir/$coq_opam_package.$RUNNER.1.*.time || true
    cat $log_dir/$coq_opam_package.$RUNNER.1.*.perf || true

    # Print the intermediate results after we finish benchmarking each OPAM package
    if [ "$coq_opam_package" = "$(echo $sorted_coq_opam_packages | sed 's/ /\n/g' | tail -n 1)" ]; then

        # It does not make sense to print the intermediate results when
        # we finished bechmarking the very last OPAM package because the
        # next thing will do is that we will print the final results.
        # It would look lame to print the same table twice.
        :
    else

        echo "DEBUG: $render_results "$log_dir" $num_of_iterations $new_coq_commit_long $old_coq_commit_long 0 user_time_pdiff $installable_coq_opam_packages"
        rendered_results="$($render_results "$log_dir" $num_of_iterations $new_coq_commit_long $old_coq_commit_long 0 user_time_pdiff $installable_coq_opam_packages)"
        echo "${rendered_results}"
        # update the comment
        coqbot_update_comment "" "${rendered_results}" ""
        msg="Benching continues..."
        if [ -n "$failed_packages" ]; then
            msg="$msg
Failed: $failed_packages
$skipped_packages"
        fi
        zulip_edit "Benching continues..."
    fi

    # N.B. Not all packages end in .dev, e.g., coq-lambda-rust uses .dev.timestamp.
    # So we use a wildcard to catch such packages.
    coq_opam_package_nover=${coq_opam_package%%.*}
    new_base_path=$(echo "$new_opam_root/ocaml-NEW/.opam-switch/build/$coq_opam_package_nover".*/)
    old_base_path=$(echo "$old_opam_root/ocaml-OLD/.opam-switch/build/$coq_opam_package_nover".*/)

    # Generate per-file comparison
    for iteration in $(seq $num_of_iterations); do
        # opam logs prefix the printing with "- " so remove that
        # remove the base path for nicer printing and so the script can identify common files
        "$program_path"/../../tools/make-both-time-files.py --real \
            <(sed -e 's/^- //' -e "s:$new_base_path::" "$log_dir/$coq_opam_package.NEW.opam_install.$iteration.stdout.log") \
            <(sed -e 's/^- //' -e "s:$old_base_path::" "$log_dir/$coq_opam_package.OLD.opam_install.$iteration.stdout.log") \
            > "$log_dir/$coq_opam_package.BOTH.perfile_timings.$iteration.log"
    done

    # Generate HTML report for LAST run

    for vo in $(cd $new_base_path/; find . -name '*.vo'); do
        if [ -e $old_base_path/$vo ]; then
          echo "$coq_opam_package/$vo $(stat -c%s $old_base_path/$vo) $(stat -c%s $new_base_path/$vo)" >> "$log_dir/vosize.log"
        fi
        if [ -e $old_base_path/${vo%%o}.timing ] && \
               [ -e $new_base_path/${vo%%o}.timing ]; then
            mkdir -p $working_dir/html/$coq_opam_package/$(dirname $vo)/
            # NB: sometimes randomly fails
            $timelog2html $new_base_path/${vo%%o} \
                                       $old_base_path/${vo%%o}.timing \
                                       $new_base_path/${vo%%o}.timing > \
                                       $working_dir/html/$coq_opam_package/${vo%%o}.html ||
                echo "Failed (code $?):" $timelog2html $new_base_path/${vo%%o} \
                     $old_base_path/${vo%%o}.timing \
                     $new_base_path/${vo%%o}.timing
        fi
    done
done

# Since we do not upload all files, store a list of the files
# available so that if we at some point want to tweak which files we
# upload, we'll know which ones are available for upload
du -ha "$working_dir" > "$working_dir/files.listing"

# The following directories in $working_dir are no longer used:
#
# - coq, opam.OLD, opam.NEW

# Measured data for each `$coq_opam_package`, `$iteration`, `status \in {NEW,OLD}`:
#
#     - $working_dir/$coq_opam_package.$status.$iteration.time
#       => output of /usr/bin/time --format="%U" ...
#
#     - $working_dir/$coq_opam_package.NEW.$iteration.perf
#       => output of perf stat -e instructions:u,cycles:u ...
#
# The next script processes all these files and prints results in a table.

# Generate per-file comparison for everything at once
new_base_path=$new_opam_root/ocaml-NEW/.opam-switch/build/
old_base_path=$old_opam_root/ocaml-OLD/.opam-switch/build/
for iteration in $(seq $num_of_iterations); do
    "$program_path"/../../tools/make-both-time-files.py --real \
        <(sed -e 's/^- //' -e "s:$new_base_path::" "$log_dir/"*".NEW.opam_install.$iteration.stdout.log") \
        <(sed -e 's/^- //' -e "s:$old_base_path::" "$log_dir/"*".OLD.opam_install.$iteration.stdout.log") \
        > "$log_dir/ALL.BOTH.perfile_timings.$iteration.log"
done

# timings data
timings=$working_dir/timings
mkdir -p $timings

# Print line by line slow downs and speed ups
if [ -d "$working_dir/html" ]; then # might not exist if all jobs failed
cd "$working_dir/html"
$render_line_results
# Move line timing files to timings folder (they will become artifacts)
mv fast_table slow_table timings_table $timings

# html tables don't get generated if the bench is run locally ie without CI variables
for f in fast_table.html slow_table.html timings_table.html; do
    if [ -f "$f" ]; then mv "$f" $timings; fi
done
fi

echo "INFO: workspace = ${CI_JOB_URL}/artifacts/browse/${bench_dirname}"

# Print the final results.
if [ -z "$installable_coq_opam_packages" ]; then
    # Tell the user that none of the OPAM-package(s) the user provided
    # /are installable.
    printf "\n\nINFO: failed to install: $sorted_coq_opam_packages"
    coqbot_update_comment "done" "" "$sorted_coq_opam_packages"
    exit 1
fi

echo "DEBUG: $render_results $log_dir $num_of_iterations $new_coq_commit_long $old_coq_commit_long 0 user_time_pdiff $installable_coq_opam_packages"
rendered_results="$($render_results "$log_dir" $num_of_iterations $new_coq_commit_long $old_coq_commit_long 0 user_time_pdiff $installable_coq_opam_packages)"
echo "${rendered_results}"
echo "${rendered_results}" > $timings/bench_summary

echo "INFO: per line timing: ${CI_JOB_URL}/artifacts/browse/${bench_dirname}/html/"

cd "$coq_dir"
echo INFO: Old Coq version
git log -n 1 "$old_coq_commit"
echo INFO: New Coq version
git log -n 1 "$new_coq_commit"

if [ -n "$failed_packages" ]; then
    not_installable_coq_opam_packages=$failed_packages
    if [ -n "$skipped_packages" ]; then
        not_installable_coq_opam_packages="$not_installable_coq_opam_packages
$skipped_packages"
    fi
else # in case the failed package detection is bugged
    not_installable_coq_opam_packages=$(comm -23 <(echo $sorted_coq_opam_packages | sed 's/ /\n/g' | sort | uniq) <(echo $installable_coq_opam_packages | sed 's/ /\n/g' | sort | uniq) | sed 's/\t//g')
fi

coqbot_update_comment "done" "${rendered_results}" "${not_installable_coq_opam_packages}"

touch $timings/bench_failures
if [ -n "$not_installable_coq_opam_packages" ]; then
    # Tell the user that some of the provided OPAM-package(s)
    # is/are not installable.
    printf '\n\nINFO: failed to install %s\n' "$not_installable_coq_opam_packages" | tee $timings/bench_failures
    zulip_edit "Bench complete, failed to install packages:
$not_installable_coq_opam_packages"
    exit 1
fi

zulip_edit "Bench complete: all packages successfully installed."
