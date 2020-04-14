#!/bin/bash

SAMPLE=proof-sample-

num=$(ls -1 ${SAMPLE}* | wc -l)
declare -A TEKST
TEKST[fs_from_tfs]="Soundness non-systematic \hfill (S1)"
TEKST[fs_from_tfs2]="Soundness non-systematic, non-duplication  \hfill (S2)"
TEKST[fs_from_tfs3]="Soundness systematic, automatic  \hfill (S3)"
TEKST[tfs_exists]="Completeness non-systematic \hfill (C1)"
TEKST[tfs_exists2]="Completeness non-systematic, non-duplication \hfill (C2)"
TEKST[tfs_exists3]="Completeness systematic, manual \hfill (C3)"
TEKST[tfs_exists4]="Completeness systematic, automatic blind \hfill (C4)"
TEKST[tfs_exists5]="Completeness systematic, well chosen \hfill (C5)"


for i in fs_from_tfs{,2,3} tfs_exists{,2,3,4,5}; do
    echo %% $i
    sumap=0
    sumaq=0
    for j in $(ls -v ${SAMPLE}*); do
        [[ -n $DEBUG ]] && grep -F "$i.v" $j
	p=`grep -F "$i.v" $j | cut -d"]" -f2 | cut -ds -f1`
        [[ -n $DEBUG ]] && echo "  p: $j -> '$p'"
	sumap=`echo "$sumap + $p" | bc -l`

        [[ -n $DEBUG ]] && (grep -A1 -F "$i.v" $j | grep Qed)
	q=`grep -A1 -F "$i.v" $j | grep Qed | cut -d"]" -f2 | cut -ds -f1`
        [[ -n $DEBUG ]] && echo "  q: $j -> '$q'"
        sumaq=`echo "$sumaq + $q" | bc -l`

    done
    echo "${TEKST[$i]} & $(cat $i.v | wc -l) & $(echo -e "scale=2\n$sumap/$num" | bc -l) & $(echo -e "scale=2\n$sumaq/$num" | bc -l) \\\\" | perl -p -e "s/ \./ 0./g"

    echo "\\hline"
    
done

