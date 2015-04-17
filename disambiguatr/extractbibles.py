#!/usr/bin/env python3

"""
Pull examples of cross-language ambiguous Quechua adjectives from the bitext
bibles.
"""

from collections import defaultdict
from os.path import expanduser
import os
import sys
import re
import copy

import spanishutil
import parsebibles
import parsefeatures
import ambiguouswords

def loadtargetwords(fn):
    """Load the target words from the specified file name. They should be
    listed one per line."""
    out = set()
    with open(fn, "r") as infile:
        for line in infile:
            line = line.strip()
            out.add(line)
    return out

def loadambiguouspairs(fn):
    """Given a file containing the (spanish, quechua) translation pairs, return
    a list of all them."""
    out = []
    with open(fn, "r") as infile:
        for line in infile:
            line = line.strip()
            splitted = line.split(" ", 1)
            sw = splitted[0]
            qw = splitted[1]
            out.append((sw, qw))
    return out

def verse_has_word(verse, word, lang):
    pat = pattern(word, lang)
    match = pat.search(verse)
    if match:
        return match.string[match.start() : match.end()]
    return False

def verses_with_words(bible, words, lang):
    """Return the set of verse ids such that the verses contain at least one of
    the target words."""
    out = set()
    pat = pattern_anyword(words)
    for verseid in bible:
        line = bible[verseid]
        if pat.search(line):
            out.add(verseid)
    return out

def pattern_anyword(words):
    """Produce a regex pattern that matches any of these words."""
    patparts = ["\\b{0}\\b".format(word) for word in words]
    regex = "|".join(patparts)
    return re.compile(regex)

patterncache = {}
def pattern(word, lang):
    """Returns the regex pattern for a string having a particular word, with
    word boundaries along the edges; use caching."""
    if (word,lang) not in patterncache:
        if lang == "es":
            ## Get all the inflections of this adjective.
            versions = spanishutil.wordversions(word)
            patparts = ["\\b{0}\\b".format(version) for version in versions]
            regex = "|".join(patparts)
        else:
            regex = "\\b{0}\\b".format(word)
        patterncache[(word,lang)] = re.compile(regex)
    return patterncache[(word, lang)]

def main():
    quechuafn = expanduser("~/corpora/bibles/999.QU.Cuzco.QuechuaCatholic")
    spanishfn = expanduser("~/corpora/bibles/061.ES.R2.ReinaValera1995")

    quechuabible = parsebibles.loadbible(quechuafn)
    spanishbible = parsebibles.loadbible(spanishfn)

    targetwords = loadtargetwords("quechuatargets")
    print("this many quechua target words: {0}".format(len(targetwords)))

    ambiguouspairs = loadambiguouspairs("ambiguouspairs")

    ## delete the testcases files, since we're about to rebuild them.
    for sw,qw in ambiguouspairs:
        fn = "testcases/{0}".format(sw)
        if os.path.exists(fn):
            os.remove(fn)

    print("finding target verses...")
    targetverses = verses_with_words(quechuabible, targetwords, "qu")

    print("loading dictionaries again...")
    esqu = ambiguouswords.spanish_to_quechua()

    observed = defaultdict(lambda:set()) # map from sw to list of qw.
    counts = defaultdict(lambda:0)
    print("finding verse pairs...")
    nskipped = 0
    for tv in sorted(targetverses):
        if tv in spanishbible:
            for (sw,qw) in ambiguouspairs:
                if (verse_has_word(quechuabible[tv], qw, "qu") and
                    verse_has_word(spanishbible[tv], sw, "es")):

                    possibilities = copy.deepcopy(esqu[sw])
                    possibilities.remove(qw)
                    if any([verse_has_word(quechuabible[tv], otherqw, "qu")
                            for otherqw in possibilities]):
                        nskipped += 1
                        continue

                    observed[sw].add(qw)
                    counts[(sw,qw)] += 1
                    inflected_sw = verse_has_word(spanishbible[tv], sw, "es")

                    mainverbs,dobjs = parsefeatures.mainverbs_and_dobjs(
                        spanishbible[tv])

                    with open("testcases/{0}".format(sw), "a") as out:
                        print("\ntestcase", file=out)
                        print("S:", spanishbible[tv], file=out)
                        print("Q:", quechuabible[tv], file=out)
                        print("s:", sw, file=out)
                        print("q:", qw, file=out)
                        print("inflected_sw:", inflected_sw, file=out)
                        print("mainverbs:", " ".join(mainverbs), file=out)
                        print("dobjs:", " ".join(dobjs), file=out)
                        print("endtestcase", file=out)
    print("skipped this many:", nskipped)

    with open("thecounts", "w") as out:
        for sw in sorted(observed.keys()):
            if (len(observed[sw]) > 1 and
                all( [counts[(sw,qw)] >= 2 for qw in observed[sw]]) ):
                for qw in sorted(observed[sw]):
                    print(sw, qw, counts[(sw,qw)], file=out)

if __name__ == "__main__": main()
