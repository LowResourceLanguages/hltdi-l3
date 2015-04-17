#!/bin/bash

GIZAPP="$HOME/software/giza-pp/GIZA++-v2/GIZA++"
PLAIN2SNT="$HOME/software/giza-pp/GIZA++-v2/plain2snt.out"
MKCLS="$HOME/software/giza-pp/mkcls-v2/mkcls"

$PLAIN2SNT source_text.txt target_text.txt
$MKCLS -psource_text.txt -Vsource_text.vcb.classes >& mkcls1.log 
$MKCLS -ptarget_text.txt -Vtarget_text.vcb.classes >& mkcls2.log
$GIZAPP -S source_text.vcb -T target_text.vcb -C source_text_target_text.snt
