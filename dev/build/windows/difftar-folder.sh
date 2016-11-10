#!/bin/bash

###################### COPYRIGHT/COPYLEFT ######################

# (C) 2016 Intel Deutschland GmbH
# Author: Michael Soegtrop
#
# Released to the public by Intel under the
# GNU Lesser General Public License Version 2.1 or later
# See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html
#
# With very valuable help on building GTK from
#   https://wiki.gnome.org/Projects/GTK+/Win32/MSVCCompilationOfGTKStack
#   http://www.gaia-gis.it/spatialite-3.0.0-BETA/mingw64_how_to.html

###################### Script safety and debugging settings ######################

set -o nounset

# Print usage

if [ "$#" -lt 1 ] ; then
  echo 'Diff a tar (or compressed tar) file with a folder'
  echo 'difftar-folder.sh <tarfile> [<folder>] [strip]'
  echo default for folder is .
  echo default for strip is 0.
  echo 'strip must be 0 or 1.'
  exit 1
fi

# Parse parameters

tarfile=$1

if [ "$#" -ge 2 ] ; then
  folder=$2
else
  folder=.
fi

if [ "$#" -ge 3 ] ; then
  strip=$3
else
  strip=0
fi

# Get path prefix if --strip is used

if [ "$strip" -gt 0 ] ; then
  prefix=`tar -t -f $tarfile | head -1`
else
  prefix=
fi

# Original folder

if [ "$strip" -gt 0 ] ; then
  orig=${prefix%/}.orig
elif [ "$folder" = "." ] ; then
  orig=${tarfile##*/}
  orig=./${orig%%.tar*}.orig
elif [ "$folder" = "" ] ; then
  orig=${tarfile##*/}
  orig=${orig%%.tar*}.orig
else
  orig=$folder.orig
fi
echo $orig
mkdir -p "$orig"


# Make sure tar uses english output (for Mod time differs)
export LC_ALL=C

# Search all files with a deviating modification time using tar --diff
tar --diff -a -f "$tarfile" --strip $strip --directory "$folder" | grep "Mod time differs" | while read -r file ; do
  # Substitute ': Mod time differs' with nothing
  file=${file/: Mod time differs/}
  # Check if file exists
  if [ -f "$folder/$file" ] ; then 
    # Extract original file
    tar -x -a -f "$tarfile" --strip $strip --directory "$orig" "$prefix$file"
    # Compute diff
    diff -u "$orig/$file" "$folder/$file" 
  fi
done