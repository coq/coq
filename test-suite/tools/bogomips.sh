#!/bin/sh

sed -n \
  -e "s/bogomips.*: \([0-9]*\).*/\1/p" `# i386, ppc` \
  -e "s/Cpu0Bogo.*: \([0-9]*\).*/\1/p" `# sparc` \
  -e "s/BogoMIPS.*: \([0-9]*\).*/\1/p" `# alpha` \
  /proc/cpuinfo \
  | head -1
