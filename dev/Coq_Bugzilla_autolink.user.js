// ==UserScript==
// @name        Coq Bugzilla autolink
// @namespace   SkySkimmer
// @include     https://github.com/coq/coq/*
// @description Makes BZ#XXXX into links to bugzilla for GitHub
// @version     1
// @grant       none
// ==/UserScript==

var regex = /BZ#(\d+)/g;
var substr = '<a href="https://coq.inria.fr/bugs/show_bug.cgi?id=$1">$&</a>';

function doNode(node)
{
    node.innerHTML = node.innerHTML.replace(regex,substr);
}

var comments = document.getElementsByClassName("comment-body");

for(var i=0; i<comments.length; i++)
{
    var pars = comments[i].getElementsByTagName("p");
    for(var j=0; j<pars.length; j++)
    {
        doNode(pars[j]);
    }
}

// usually 1 or 0 titles...
var titles = document.getElementsByClassName("js-issue-title");
for(var i=0; i<titles.length; i++)
{
    doNode(titles[i]);
}
