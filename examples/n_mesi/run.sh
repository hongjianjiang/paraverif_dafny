#!/bin/bash
shopt -s expand_aliases
startTime=`date +%Y%m%d-%H:%M:%S`
startTime_s=`date +%s`
dafny n_mesi_lemma_oninv__1.dfy
dafny n_mesi_lemma_oninv__2.dfy
dafny n_mesi_lemma_oninv__3.dfy
endTime=`date +%Y%m%d-%H:%M:%S`
endTime_s=`date +%s`

sumTime=$[ $endTime_s - $startTime_s ]

echo "$startTime ---> $endTime" "Total:$sumTime seconds"