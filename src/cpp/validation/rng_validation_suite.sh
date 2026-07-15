#!/bin/bash
#
# LICENSE: CC0
#
# To the extent possible under law, the person who associated CC0 with
# this project has waived all copyright and related or neighboring rights
# to this project.
#
# You should have received a copy of the CC0 legalcode along with this
# work.  If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
#

#
# simple validation for random instances (poisson process)
# of Relative Neighborhood Graph in 2d and 3d.
#
# creates M=1000 instaces each of 2d and 3d RNG for n=10,100,1000,10000
# compares the Shrinking Posts on Increasing Fence (SPoIF) algorithm against
# the naive RNG algorithm.
#
# If there's a discrepency, the validation script terminates with error.
#

n0=10
N1=100000
N1=10000

sn=10

M=1000

n=$n0

spoif="../bin/spoif"

every=100

while [[ $n -le $N1 ]] ; do
  echo "# n:$n"

  for seed in `seq $M` ; do

    c=`echo "$seed % $every" | bc`
    if [[ $c -eq 0 ]] ; then
      echo "# n:$n, $seed / $M passed (dim 2,3)"
    fi

    for dim in `seq 2 3` ; do

      sha0=` $spoif -n $n -d $dim -S $seed | sha256sum | cut -f1 -d ' ' `
      sha1=` $spoif -n $n -d $dim -S $seed -A naive | sha256sum | cut -f1 -d ' ' `

      if [[ "$sha0" != "$sha1" ]] ; then
        echo "FAIL! n:$n dim:$dim seed:$seed ($sha0 != $sha1)"
        exit -1
      fi

    done

  done

  n=`echo "$n * $sn" | bc`
done

exit 0
