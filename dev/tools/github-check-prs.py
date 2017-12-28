#!/usr/bin/env python3

# Requires PyGithub https://pypi.python.org/pypi/PyGithub
from github import Github

REPO = "coq/coq"
REBASE_LABEL="needs: rebase"

token = input("Github access token: ")

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
    elif dirty and not labelled:
        print ("PR #" + str(pull.number) + " is dirty and not labelled")
    else:
        # give some feedback so the user can see we didn't crash
        print ("PR #" + str(pull.number) + " OK")
