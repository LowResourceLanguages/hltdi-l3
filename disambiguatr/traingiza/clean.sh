#!/bin/bash

echo "Delete all these files?"
ls *.log *.snt *.vcb *.classes *.cats *.final *.config *.gizacfg *.perp

read -p "y/n ?? "
if [ "$REPLY" == "y" ] ; then
  rm *.log *.snt *.vcb *.classes *.cats *.final *.config *.gizacfg *.perp
fi
