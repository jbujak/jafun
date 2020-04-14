#!/bin/bash

UPTO=${1:-9}
FROM=${2:-0}

SAMPLE=proof-sample-

for i in $(seq $FROM $UPTO); do
	echo -----sample $i
	rm -f JaChurchMeasure.vo
	coqc -time JaChurchMeasure.v > ${SAMPLE}${i}
        perl -00 -pi -e 's/[0-9]+\.[0-9]* secs \([0-9]+\.[0-9]*u,[0-9]+\.[0-9]*s\)\n(?=[0-9])//g' ${SAMPLE}${i}
done

# The perl line above transforms strange output:
#   Chars 19987 - 19991 [Qed.] 0.384 secs (0.38u,0.s)
#   0.17 secs (0.168u,0.s)
# into
#   Chars 19987 - 19991 [Qed.] 0.17 secs (0.168u,0.s)
# This is because the first number is too corelated with Load time (always +-10%), so this is probably a glitch in measurement output

# 
# -00 whole file at once
# (?=[0-9]) - before a digit
