// ==UserScript==
// @name        Bugzilla Coq autolink
// @namespace   CoqScript
// @include     https://coq.inria.fr/bugs/*
// @description Makes #XXXX into links to Github Coq PRs
// @version     1
// @grant       none
// ==/UserScript==

var regex = /#(\d+)/g;
var substr = '<a href="https://github.com/coq/coq/pull/$1">$&</a>';

function doNode(node)
{
    node.innerHTML = node.innerHTML.replace(regex,substr);
}

var comments = document.getElementsByClassName("bz_comment_table")[0];
var pars = comments.getElementsByClassName("bz_comment_text");

for(var j=0; j<pars.length; j++)
{
    doNode(pars[j]);
}

