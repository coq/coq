#!/bin/bash

echo `find . -name "*.xml"` | uris_of_filenames.pl > index.txt
