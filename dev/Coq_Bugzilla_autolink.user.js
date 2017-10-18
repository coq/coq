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

function doTitle(node)
{
    node.innerHTML = node.innerHTML.replace(regex,substr);
}

function filter(node)
{
  if (node.nodeName == '#text')
    {
      return NodeFilter.FILTER_ACCEPT;
    }
  else if(node.nodeName == 'A')
    {
      return NodeFilter.FILTER_REJECT;
    }
  return NodeFilter.FILTER_SKIP;
}
var comments = document.getElementsByClassName("comment-body");

function doNode(parent)
{
    var nodes = document.createTreeWalker(parent,NodeFilter.SHOW_ALL,{ acceptNode : filter },false);
    var node;
    while(node=nodes.nextNode())
    {
      var content = node.textContent;
      var matches = regex.exec(content);

      if(matches && matches.length > 1)
      {
        var range = document.createRange();
        var start = content.search(regex);
        var end = start + matches[0].length;
        range.setStart(node, start);
        range.setEnd(node, end);
        var linkNode = document.createElement("a");
        linkNode.href = "https://coq.inria.fr/bugs/show_bug.cgi?id=" + matches[1];
        range.surroundContents(linkNode);

        //handle multiple matches in one text node
        doNode(linkNode.parentNode);
      }
    }
}

for(var i=0; i<comments.length; i++)
{
  doNode(comments[i]);
}

// usually 1 or 0 titles...
var titles = document.getElementsByClassName("js-issue-title");
for(var i=0; i<titles.length; i++)
{
    doTitle(titles[i]);
}
