#!/usr/bin/env python3

# Requires PyGithub https://pypi.python.org/pypi/PyGithub, for instance
# debian package: python3-github
# nix: nix-shell -p python3 python3Packages.PyGithub --run ./github-check-rebase.py
from github import Github
import argparse

REPO = "coq/coq"
REBASE_LABEL="needs: rebase"

parser = argparse.ArgumentParser()
parser.add_argument("--token-file", type=argparse.FileType('r'))
args = parser.parse_args()

if args.token_file is None:
    token = input("Github access token: ").strip()
else:
    token = args.token_file.read().rstrip("\n")
    args.token_file.close()

if token == "":
    print ("Warning: using the GitHub API without a token")
    print ("We may run into rate limit issues")
    g = Github()
else:
    g = Github(token)

repo = g.get_repo(REPO)

for pull in repo.get_pulls():
    # if conflicts then dirty
    # otherwise blocked (because I have no rights)
    dirty = pull.mergeable_state == "dirty"
    labelled = False
    for label in repo.get_issue(pull.number).get_labels():
        if label.name == REBASE_LABEL:
            labelled = True
    if labelled and not dirty:
        print ("PR #" + str(pull.number) + " is not dirty but is labelled")
        print ("("+ pull.html_url +")")
    elif dirty and not labelled:
        print ("PR #" + str(pull.number) + " is dirty and not labelled")
        print ("("+ pull.html_url +")")
    else:
        # give some feedback so the user can see we didn't crash
        print ("PR #" + str(pull.number) + " OK")
