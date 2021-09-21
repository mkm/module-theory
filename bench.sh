#!/bin/bash

for dataset in sparse dense; do
    echo Dataset $dataset
    for impl in multi binary; do
        echo $impl
        size=1
        elapsed=0.0
        while [ 0 -ne $(bc <<<"$elapsed < 1") ]; do
            prevelapsed=$elapsed
            elapsed=$(./Benchmark $impl$dataset $size +RTS -s 2>&1 | awk '/Total/{sub(/s/, "", $3); print $3}')
            if [ 0 -ne $(bc <<<"$elapsed > 0.01") ]; then
                ratio=$(bc <<<"scale=2; sqrt($elapsed / $prevelapsed)")
                echo "$elapsed | $ratio | $size"
            fi
            prevsize=$size
            size=$(bc <<<"$size * 2")
        done
    done
    echo
done
