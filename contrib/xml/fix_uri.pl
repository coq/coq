#!/usr/bin/perl -w

################################################################################
#                                                                              #
#                                PROJECT HELM                                  #
#                                                                              #
#                      A tactic to print Coq objects in XML                    #
#                                                                              #
#                 Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>                #
#                                  20/12/2000                                  #
#                                                                              #
# This module script takes from stdin two list of uris of xml files containing #
# uris to each other. The uris in the second list are broken because each uri  #
# is only the suffix of the right one that appear in the first list.           #
# The script modifies all the files in the second list fixing the uris.        #
#                                                                              #
# Assumptions:                                                                 #
#  1) no more than one uri per line                                            #
#  2) all uris have this format: "cic:/section/term"                           #
#     where there are no "/" in term                                           #
#                                                                              #
################################################################################

use strict;

my %name_to_uri;

open(FD1,$ARGV[0]);
my @Argv = <FD1>;
close(FD1);

open(FD1,$ARGV[1]);
my @savedArgv = <FD1>;
close(FD1);

my @Argv2;
my $tmpi = 0;
for (my $i = 0; $i <= $#Argv; $i++) {
 chomp($Argv[$i]);
 $Argv[$i] =~ s/^cic:\/(.*)/$1.xml/;
 $Argv2[$tmpi++] = $Argv[$i] if !($Argv[$i] =~ /^theory:/);
}

my @savedArgv2;
$tmpi = 0;
for (my $i = 0; $i <= $#savedArgv; $i++) {
 chomp($savedArgv[$i]);
 $savedArgv[$i] =~ s/^cic:\/(.*)/$1.xml/;
 $savedArgv2[$tmpi++] = $savedArgv[$i] if !($savedArgv[$i] =~ /^theory:/);
}

# phase 1: fill %name_to_uri

print "phase 1: collecting uris\n";

for my $i (@Argv2) {
 if ($i =~ /.*\.(con|ind|var)\.xml/) {
  my $j = $i;
  $j =~ s/.*\/(.*)\.xml$/$1/;         # get file name
  $i =~ s/(\.\/)?(.*)\.xml/$2/;       # get uri
  my @tmp;
  if (defined (my $urisref = $name_to_uri{$j}))
   { @tmp = @$urisref; }
  else
   { @tmp = (); }
  push(@tmp, $i);
  $name_to_uri{$j} = \@tmp;
 }
}

# phase 2: repair the uris in all files

print "phase 2: repairing uris\n";

for my $i (@savedArgv2) {
print "Processing $i\n";
 open (FDi, "<$i") or die "critical error: file $i does not exist!\n";
 open (FDo, ">$i.new") or die "critical error: file $i.new could not be created!\n";
 while(<FDi>) {
  if (/"cic:(.*)"/) {
   my ($origline, $line, $filename) = ($_, $_, $_);
   chomp ($filename);
   $filename =~ s/(.*)"cic:([^"]*)"(.*)/$2/;
   my $section = $filename;
   $filename =~ s/.*\/(.*)$/$1/;                        # get file name
   $section  =~ s/(.*)\/(.*)$/$1/;			# get section
   if (defined (my $urisref = $name_to_uri{$filename})) {
    my @uris = @$urisref;
    my $uri;
    for (my $h = 0; $h <= $#uris; $h++) {
     my $huri = $uris[$h];
     if (index("/$huri", "$section/") >= 0) {
      if (!defined($uri)) {
       $uri = $huri;
      } else {
       print "uri scelta a caso per il termine $filename nel file $i\n";
       print "la prima scelta era $uri\nla seconda $huri\n";
       print "la sezione era $section\n\n";
      }
     }
    }
    if (!defined($uri)) {
     print "Due to internal error uri which filename is $filename in file $i can't be repaired!\n";
     $line = $origline;
    } else {
     $line =~ s/(.*)"cic:([^"]*)"(.*)/$1"cic:\/$uri"$3/;
    }
    print FDo "$line";
   } else {
    print "uri which filename is $filename in file $i can't be repaired!\n";
    print FDo $origline;
   }
  } else {
   print FDo;
  }
 }
 close (FDi);
 close (FDo);
 rename("$i.new", "$i");
}
