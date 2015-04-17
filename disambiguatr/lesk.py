#!/usr/bin/env python3

"""Cross-lingual version of the Lesk algorithm. Based on "Simplified Lesk",
from Kilgarriff and Rosenzweig (2000).

The approach is like this: given a source-language context, we have to pick a
target-language word type.

But we have target-to-source dictionary entries for each possible
target-language word type. So at decision time, we choose the target-language
word type whose dictionary entry has the most overlap with the context for the
instance in question.
"""

## Here's the algorithm from that paper.
# (a) For each sense s of that word,
# (b) set weight(s) to zero.
# (c) Identify set of unique words W in surrounding sentence.
# (d) For each word w in W,
# (e)  for each sense s of the word to be tagged,
# (f)   if w occurs in the definition or example sentences of s,
# (g)     add weight(w) to weight(s).
# (h) Choose the sense with greatest weight(s)
## weights can be set in different ways:
## - dumb: weight is 1
## - idf of each term, where every entry in the dictionary is a "document"

from collections import defaultdict
import math

from learner import Learner
import spanishutil

## If true, do stemming before word comparison.
LESK_STEMMING = True

## True:
#Overall!!
#  accuracy: 762 / 1156 = 0.659
#  disagreed: 246 / 1156 = 0.213
#  disagree accuracy: 49 / 246 = 0.199
#  if picking uniformly: 0.389
# this many bails: 288

## False:
# Overall!!
#   accuracy: 636 / 1156 = 0.550
#   disagreed: 363 / 1156 = 0.314
#   disagree accuracy: 45 / 363 = 0.124
#   if picking uniformly: 0.389
# this many bails: 545

class Lesk(Learner):
    def __init__(self, xs):
        self.classes = set()
        class_counts = defaultdict(lambda:0)

        for x in xs:
            self.classes.add(x.cl)
            class_counts[x.cl] += 1

        maxcount = max(class_counts.values())
        self.maxclass = [cl for cl,count in class_counts.items()
                            if count == maxcount][0]
    def __call__(self, x):
        weights = defaultdict(lambda:0)

        ## get the text of the instance as a set of words.
        context = spanishutil.normalize_split(x.text)
        context = spanishutil.remove_stopwords(context)
        if LESK_STEMMING:
            context = spanishutil.stem_words(context)
        context = set(context)

        for cl in self.classes:
            for sw in set(qu_entries[cl].split()):
                if sw in context:
                    # print("here's a match:", sw)
                    weights[cl] += es_idfs[sw]

        maxweight = max([0] + list(weights.values()))
        if maxweight == 0:
            # print("bailing out, no match.")
            return self.maxclass

        best = [cl for cl,weight in weights.items()
                   if weight == maxweight][0]
        return best

    @staticmethod
    def Initialize():
        print("Loading data for Lesk...")
        load_entries()


## mapping from Quechua words to ("dictionary entry", idf).
qu_entries = defaultdict(lambda:"")
es_idfs = defaultdict(lambda:0)

ques_fn = "dictionaries/DicAMLQuechua-qu.txt"
def load_entries():
    termcounts = defaultdict(lambda:1)
    terms = set()

    with open(ques_fn) as infile:
        for line in infile:
            if "." not in line: continue
            qw, entry = line.split(".", 1)
            entry = entry.strip()

            words = spanishutil.normalize_split(entry)
            words = spanishutil.remove_stopwords(words)

            if LESK_STEMMING:
                words = spanishutil.stem_words(words)
            qu_entries[qw] = " ".join(words)
            for sw in set(words):
                termcounts[sw] += 1
                terms.add(sw)

    n_entries = len(qu_entries)
    for sw in terms:
        es_idfs[sw] = math.log(n_entries / termcounts[sw])
    print("OK loaded data for Lesk.")

def main():
    print(qu_entries["yuyu"])
    print(es_idfs[spanishutil.stem("alpaca")])
    print(es_idfs[spanishutil.stem("perro")])
    print(es_idfs[spanishutil.stem("y")])

if __name__ == "__main__": main()
