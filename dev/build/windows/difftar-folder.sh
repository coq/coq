#!/bin/bash

###################### COPYRIGHT/COPYLEFT ######################

# (C) 2016 Intel Deutschland GmbH
# Author: Michael Soegtrop
#
# Released to the public by Intel under the
# GNU Lesser General Public License Version 2.1 or later
# See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

###################### DIFF A TAR FILE AND A FOLDER ######################

set -o nounset

# Print usage

if [ "$#" -lt 2 ] ; then
  echo 'Diff a tar (or compressed tar) file with a folder'
  echo 'difftar-folder.sh <tarfile> <folder> [strip]'
  echo '<tarfile> is the name of the tar file do diff with (required)'
  echo '<folder> is the name of the folder to diff with (required)'
  echo '<strip> is the number of path components to strip from tar file (default is 0)'
  echo 'All files in the tar file must have at least <strip> path components.'
  echo 'This also adds new files from folder.new, if folder.new exists'
  exit 1
fi

# Parse parameters

tarfile=$1
folder=$2

if [ "$#" -ge 3 ] ; then
  strip=$3
else
  strip=0
fi

# Get path prefix if --strip is used

if [ "$strip" -gt 0 ] ; then
  # Get the path/name of the first file from teh tar and extract the first $strip path components
  # This assumes that the first file in the tar file has at least $strip many path components
  prefix=$(tar -t -f "$tarfile" | head -1 | cut -d / -f -$strip)/
else
  prefix=
fi

# Original folder

orig=$folder.orig
mkdir -p "$orig"

# New amd empty filefolder

new=$folder.new
empty=$folder.empty
mkdir -p "$empty"

# Print information (this is ignored by patch)

echo diff/patch file created on "$(date)" with:
echo difftar-folder.sh "$@"
echo TARFILE=    "$tarfile"
echo FOLDER=     "$folder"
echo TARSTRIP=   "$strip"
echo TARPREFIX=  "$prefix"
echo ORIGFOLDER= "$orig"

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

if [ -d "$new" ] ; then
  diff -u -r --unidirectional-new-file "$empty" "$new"
fi
