#!/usr/bin/env python3

import sys
import re
from operator import itemgetter

import l3
import spanishutil
import eswn
import bagofwords
from infogain import infogain
from mostfrequent import mostfrequent
from learner import Learner

VERBOSE = False
def vprint(*args, **kwargs):
    if VERBOSE:
        print(*args, **kwargs)

class KnnInstance:
    """Extends the more general Instance object."""

    def __init__(self, inst):
        """Takes a regular Instance object and initializes based on that."""
        self.text = inst.text
        self.sw = inst.sw
        self.qw = inst.qw
        self.inflected_sw = inst.inflected_sw

        self.paths = []
        self.calcfeatures()

    def calcfeatures(self):
        splitted = spanishutil.justletters(self.text.lower()).split()
        sw_index = splitted.index(spanishutil.justletters(self.inflected_sw))

        ## window of three words before and after
        for offset in range(-3, 4):
            index = (sw_index + offset)
            if index in range(0, len(splitted)) and index != sw_index:
                stemmed = spanishutil.stem(splitted[index])
                self.paths += eswn.hypernym_paths(stemmed)

        self.prev = None
        self.nw = None
        self.prevstemmed = None
        self.nwstemmed = None
        if sw_index != 0:
            self.prev = splitted[sw_index - 1]
            self.prevstemmed = spanishutil.stem(splitted[sw_index - 1])
        if sw_index + 1 in range(0, len(splitted)):
            self.nw = splitted[sw_index + 1]
            self.nwstemmed = spanishutil.stem(splitted[sw_index + 1])

        if self.paths != []:
            vprint("YES WN ENTRY")
        else:
            vprint("NO WN ENTRY.")

def ancestor_distance(path1, path2):
    """Returns the shortest distance to a common ancestor."""
    def find_ancestor(p1, p2):
        for i,elt in enumerate(p1):
            if elt in p2:
                return i
        return 10 + max(len(p1), len(p2))
    return find_ancestor(path1,path2) + find_ancestor(path2,path1)

knn_cache = {}
def knninstance(instance):
    """Caching wrapper around constructor for KnnInstance objects."""
    if instance not in knn_cache:
        knn_cache[instance] = KnnInstance(instance)
    return knn_cache[instance]

class KnnWithWordnet(Learner):
    def __init__(self, xs):
        self.xs = [knninstance(x) for x in xs]

    @staticmethod
    def distance(x1, x2):
        paths1 = x1.paths
        paths2 = x2.paths

        distances = [100]
        for p1 in paths1:
            for p2 in paths2:
                ancdist = ancestor_distance(p1, p2)
                distances.append(ancdist)

        ## are these actually useful?
        if x1.prev == x2.prev and (x2.prev is not None):
            distances.append(0) ## the two spanish words are the same.
            vprint("EXACT MATCH BEFORE")
        if x1.nw == x2.nw and (x2.nw is not None):
            distances.append(0) ## the two spanish words are the same.
            vprint("EXACT MATCH AFTER")
        if x1.prevstemmed == x2.prevstemmed and (x2.prevstemmed is not None):
            vprint("STEMMED MATCH BEFORE")
            distances.append(1) ## arbitrary: distance of 1 for stemmed words
                                ## being equal.
        if x1.nwstemmed == x2.nwstemmed and (x2.nwstemmed is not None):
            vprint("STEMMED MATCH AFTER")
            distances.append(1) ## arbitrary: distance of 1 for stemmed words
                                ## being equal.
        return min(distances)

    def __call__(self, x):
        x = knninstance(x)
        distances = [self.distance(other, x) for other in self.xs]
        pairs = zip(distances,self.xs)
        inorder = sorted(pairs, key=itemgetter(0))

        K = 3
        neighbors = [pair[1] for pair in inorder[:K]]
        classes = [neighbor.qw for neighbor in neighbors]
        distances = [pair[0] for pair in inorder[:K]]

        if distances[0] == 100:
            vprint("NO MATCH IN KNN", end=" ")
            out = mostfrequent([x.qw for x in self.xs])
            vprint(x.qw == out)
            return out
        else:
            nonhundred = [d for d in distances if d != 100]
            vprint("FOUND SOME IN KNN:", len(nonhundred), end=" ")

        out = mostfrequent([neighbor.qw for neighbor in neighbors])
        vprint(x.qw == out)
        return out

class KnnWordFeatures(Learner):
    def __init__(self, xs):
        sentences = [x.text for x in xs]
        classes = [x.qw for x in xs]

        features = bagofwords.wordfeatures(sentences)
        features = features.union(bagofwords.parsefeatures(xs))
        self.features = features
        self.xs = [bagofwords.bowinstance(x, self.features) for x in xs]

        featureweights = {}
        for feat in self.features:
            featureweights[feat] = infogain(self.xs, feat)
        self.featureweights = featureweights

    def __call__(self, x):
        xinst = bagofwords.bowinstance(x, self.features)
        distances = [self.distance(other, xinst) for other in self.xs]

        pairs = zip(distances,self.xs)
        inorder = sorted(pairs, key=itemgetter(0))

        K = 3
        neighbors = [pair[1] for pair in inorder[:K]]
        classes = [neighbor.qw for neighbor in neighbors]
        distances = [pair[0] for pair in inorder[:K]]

        return mostfrequent([neighbor.qw for neighbor in neighbors])

    def distance(self, x1, x2):
        dist = 0
        for feat in self.features:
            if x1.attributes[feat] != x2.attributes[feat]:
                # uniform weight
                # dist += 1
                dist += self.featureweights[feat]
        return dist
