#!/bin/bash
# Build the given modules (and their in-project dependencies) under a
# memory cap; print the exit status explicitly.
#
mem=${MEM:-6G}
systemd-run --user --scope -q -p MemoryMax=$mem -p MemorySwapMax=0 \
  lake build "$@"
rc=$?
echo "EXIT $rc"
exit $rc
