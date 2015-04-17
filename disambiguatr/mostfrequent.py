#!/usr/bin/env python3

import re
import sys

from learner import Learner

class MostFrequentBaseline(Learner):
    def __init__(self, xs):
        """Find the most frequent qw out of these training instances and build
        a classifier that always returns that as its answer."""
        classes = [x.qw for x in xs]
        self.answer = mostfrequent(classes)

    def __call__(self, x):
        return self.answer

## Sort of terrible: gets its filename from sys.argv[2].
class MostFrequentOverText(Learner):
    """Classifier that always returns the MFS, but considering the whole text,
    not just the instances in the ambiguous pairs we extracted."""

    def __init__(self, xs):
        """Find the most frequent qw out of these training instances and build
        a classifier that always returns that as its answer."""

        classes = [x.qw for x in xs]
        uniqueclasses = sorted(set(classes))

        counts = [self.count(cl) for cl in uniqueclasses]
        greatest = max(counts)
        greatestindex = counts.index(greatest)
        self.answer = uniqueclasses[greatestindex]

    countcache = {}
    @staticmethod
    def count(qw):
        cache = MostFrequentOverText.countcache
        if qw not in cache:
            regex = r"\b{0}\b".format(qw)
            with open(sys.argv[2], "r") as infile:
                text = infile.read()

            pat = re.compile(regex)
            matches = pat.findall(text)
            cache[qw] = len(matches)
            print(" ", qw, "happens", cache[qw], "times")
        return cache[qw]

    def __call__(self, x):
        return self.answer

def mostfrequent(elts):
    """Given a list, return the most frequent element in the list."""
    uniques = list(set(elts))
    counts = [elts.count(elt) for elt in uniques]
    return uniques[counts.index(max(counts))]

