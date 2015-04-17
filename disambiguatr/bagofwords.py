#!/usr/bin/env python3

"""
Bag of words features, suitable for NB and other classifiers.
"""

from collections import defaultdict

import spanishutil
from spanishutil import stem
from spanishutil import justletters
import eswn

## Flag to control whether we mark words as being in the left context or right
## context.
USESIDES = True

## Flag to control whether we expand with synsets.
USESYNSETS = False

## Flag to control whether we use parse features.
USEPARSE = True

def parsefeatures(xs):
    """Given a list of Instance objects, produce a set of all the mainverb and
    dobj features."""
    mainverbs = []
    dobjs = []
    for x in xs:
        for mv in x.mainverbs:
            mainverbs.append("mainverb:" + mv)
        for dobj in x.dobjs:
            dobjs.append("dobj:" + dobj)
    return set(mainverbs + dobjs)

def wordfeatures(sentences):
    """Given a list of strings, each of which is a sentence in Spanish, produce
    a set of the features we're going to use in classifying. (this will just
    be a set of strings, stemmed Spanish words."""

    features = set()
    for sent in sentences:
        splitted = justletters(sent.lower()).split()
        stemmed = [stem(sw) for sw in splitted
                            if sw not in spanishutil.stopwords]

        if USESYNSETS:
            for sw in stemmed:
                hypernyms = eswn.hypernym_bigset(sw)
                lefthypers = ["l:" + hn for hn in hypernyms]
                righthypers = ["r:" + hn for hn in hypernyms]
                for hn in lefthypers + righthypers:
                    features.add(hn)

        ## add left and right flags.
        if USESIDES:
            leftflagged = [ "l:" + sw for sw in stemmed]
            rightflagged = [ "r:" + sw for sw in stemmed]
            for sw in leftflagged + rightflagged:
                features.add(sw)
        else:
            for sw in stemmed:
                features.add(sw)
    return frozenset(features)

### def splitfeatures(pairs):
###     """Given a list of pairs (class,text), produce the set of features we're
###     going to use in classifying: all the words that appear in exactly one class.
###     This is ripe for overfitting."""
### 
###     featurestoclasses = defaultdict(lambda: set())
###     sentences = [sent for (cl,sent) in pairs]
### 
###     features = wordfeatures(sentences)
### 
###     for (cl, sent) in pairs:
###         splitted = justletters(sent.lower()).split()
###         stemmed = [stem(sw) for sw in splitted
###                             if sw not in spanishutil.stopwords]
###         for sw in stemmed:
###             featurestoclasses[sw].add(cl)
### 
###     out = set()
###     for feat in featurestoclasses.keys():
###         if len(featurestoclasses[feat]) == 1:
###             out.add(feat)
###     return frozenset(out)

bow_cache = {}
def bowinstance(instance, features):
    """Caching wrapper around constructor for KnnInstance objects."""
    if instance not in bow_cache:
        bow_cache[(instance,features)] = BagOfWordsInstance(instance, features)
    return bow_cache[(instance,features)]

WIDTH = 5
class BagOfWordsInstance:
    def __init__(self, inst, features):
        """Given a regular Instance, initialize this BagOfWordsInstance."""
        splitted = justletters(inst.text.lower()).split()

        stemmed = [stem(sw) for sw in splitted
                            if sw not in spanishutil.stopwords]
        sw_index = stemmed.index(stem(justletters(inst.inflected_sw)))

        leftwindow = stemmed[max(0,sw_index - WIDTH) : sw_index]
        rightwindow = stemmed[1+sw_index : min(len(stemmed),1+sw_index+WIDTH)]

        if USESIDES:
            leftwindow = ["l:" + sw for sw in leftwindow]
            rightwindow = ["r:" + sw for sw in rightwindow]

        window = leftwindow+rightwindow
        assert window != []

        if USEPARSE:
            for mainverb in inst.mainverbs:
                window.append("mainverb:" + mainverb)
            for dobj in inst.dobjs:
                window.append("dobj:" + dobj)

        if USESYNSETS:
            ## XXX(alexr): assumes that USESIDES is true.
            hypernym_window = set()
            for sw in window:
                side = sw[:2]
                word = sw[2:]
                hypernyms = eswn.hypernym_bigset(word)
                for hn in hypernyms:
                    hypernym_window.add(side + hn)
            window += list(hypernym_window)
        self.attributes = {}
        for xi in features:
            self.attributes[xi] = 1 if xi in window else 0
        self.cl = inst.qw
        self.qw = inst.qw

def main():
    verses = ["»¿Le has dado tú sus hermosas alasal pavo real\
      o sus alas y plumas al avestruz?",
     "Este desampara en la tierra sus huevos, los calienta sobre el polvo",
     "y olvida que el pie los puede pisar y que una fiera del\
     campopuede aplastarlos."]
    print(wordfeatures(verses))

if __name__ == "__main__":
    main()
