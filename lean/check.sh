#!/bin/bash
# Check one Lean file under a memory cap; print the exit status
# explicitly since systemd-run OOM kills are otherwise silent.
#
mem=${MEM:-6G}
systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 \
  lake env lean "$@"
rc=$?
echo "EXIT $rc"
exit $rc
