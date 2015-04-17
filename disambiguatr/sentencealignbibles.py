#!/usr/bin/env python3

"""
Tool to produce sentence-level alignments from the bibles, suitable for
training giza++.

The first commandline argument is the source language, second is the target
language. Produces the files traingiza/{source,target}_text.txt.

I run it like this:
$ ./sentencealignbibles.py \
  ~/corpora/bibles/061.ES.R2.ReinaValera1995 \
  ~/corpora/bibles/999.QU.Cuzco.QuechuaCatholic
"""

import sys
import string

import parsebibles
import spanishutil

allpunct = spanishutil.spanishpunct + string.punctuation
## take out ' because it's important in Quechua spelling.
allpunct = allpunct.replace("'", "")

def splitpunctuation(s):
    for p in allpunct:
        s = s.replace(p, " " + p + " ")
    return s.strip()

def main():
    assert len(sys.argv) == 3

    srcbible = parsebibles.loadbible(sys.argv[1])
    targetbible = parsebibles.loadbible(sys.argv[2])

    srcverses = set(srcbible.keys())
    targetverses = set(targetbible.keys())
    verses = srcverses.intersection(targetverses)

    multiplesentences = 0
    longverses = 0
    included = 0
    total = len(verses)
    with open("traingiza/source_text.txt", "w") as src:
        with open("traingiza/target_text.txt", "w") as trg:
            for verse in sorted(verses):
                srcverse = splitpunctuation(srcbible[verse]).lower()
                trgverse = splitpunctuation(targetbible[verse]).lower()

                srcsplitted = srcverse.split()
                trgsplitted = trgverse.split()

                ## Skip the long sentences.
                if max(len(srcsplitted), len(trgsplitted)) > 40:
                    longverses += 1
                    continue

                ## Skip the verses that seem to contain multiple sentences.
                if " . " in srcverse or " . " in trgverse:
                    multiplesentences += 1
                    continue
                print(srcverse, file=src)
                print(trgverse, file=trg)
                included += 1
    print("# too long:", longverses)
    print("# multiple sentences:", multiplesentences)
    print("# included:", included)
    print("# total:", total)

if __name__ == "__main__": main()
