#!/usr/bin/env python3

"""
Naive bayes classification.

Takes a training set and a test set, each as a csv file, and learns a naive
bayes classifier based on the training set. Then run the classifier against
each member of the test set and print out the accuracy.

For the values in the csvs, the first value is the class of that instance; the
rest are the attributes that we'll use for classification. (all instances
should have the same number of attributes)
"""

from collections import defaultdict
from functools import reduce

import bagofwords
from learner import Learner

class NaiveBayes(Learner):
    def __init__(self, xs):
        sentences = [x.text for x in xs]
        classes = [x.qw for x in xs]

        features = bagofwords.wordfeatures(sentences)
        features = features.union(bagofwords.parsefeatures(xs))

        self.xs = [bagofwords.bowinstance(x, features) for x in xs]
        self.features = features

        self.classprobs, self.attributeprobs = estimate_probabilities(self.xs)

    def __call__(self, x):
        xinst = bagofwords.bowinstance(x, self.features)
        return classify(xinst, self.classprobs, self.attributeprobs)

    def scores(self, x):
        xinst = bagofwords.bowinstance(x, self.features)
        return probscores(xinst, self.classprobs, self.attributeprobs)

## TODO: add the m-estimates, so we can get something like smoothing here too.
def estimate_probabilities(training):
    """Estimate the probability of each attribute value, given each class, from
    the training data. Returns a pair of dictionaries:
    
    The first is the "class probabilities", and goes from classes to
    probabilities.
    
    The second is the "attribute probabilities" and goes from
    (cl,attribute-pos,attribute-value) to probabilities."""

    attributecounts = defaultdict(lambda:0)
    classcounts = defaultdict(lambda:0)

    # x is an instance in the training set.
    for x in training:
        cl = x.cl
        classcounts[cl] += 1

        for k,xi in x.attributes.items():
            attributecounts[(cl, k, xi)] += 1
        # for (pos,xi) in zip(range(len(x.attributes)), x.attributes):
        #     attributecounts[(cl, pos, xi)] += 1

    classprobs = {}
    n = len(training)
    for cl in classcounts.keys():
        classprobs[cl] = classcounts[cl] / n

    ## probability of seeing that field assigned that value, given that it's a
    ## member of that class.
    # If we've never seen this before, stupidly assume 1/million. If I was
    # cooler, would do sensible smoothing.
    attributeprobs = defaultdict(lambda:(1/1000000)) 
    # attributeprobs = {}

    ## one key for each combination of class, attribute, value.
    ## Value is the ...
    for key in attributecounts.keys():
        attributeprobs[key] = attributecounts[key] / classcounts[key[0]]
    return classprobs, attributeprobs

def product(nums):
    return reduce(lambda x,y: x*y, nums)

def probscores(instance, class_probs, attribute_probs):
    """Return a list of (class, prob) tuples, representing our probability
    estimates that this instance belongs to this class."""
    possible_cls = list(class_probs.keys())
    attr_pairs = instance.attributes.items()
    out = [(class_probs[cl] * 
             product([attribute_probs[(cl, key, value)]
                for (key,value) in attr_pairs]))
           for cl in possible_cls]
    return out

def classify(instance, class_probs, attribute_probs):
    """Return a classification for this instance, given the class probabilities
    and attribute probabilities."""

    possible_cls = list(class_probs.keys())
    attr_pairs = instance.attributes.items()
    scores = [(class_probs[cl] * 
               product([attribute_probs[(cl, key, value)] for (key,value) in attr_pairs])
               ) for cl in possible_cls]

    # print(scores)
    maxindex = scores.index(max(scores))
    return possible_cls[maxindex]

class NBInstance:
    """An instance has a class (cl) and a list of attributes."""
    def __init__(self, cl, attributes):
        self.cl = cl
        self.attributes = attributes

def load_dataset(fn):
    with open(fn) as infile:
        lines = infile.readlines()
        out = []
        for line in lines:
            splitted = line.strip().split(",") 
            cl = splitted[0]
            attributes = {}
            for k,v in enumerate(splitted[1:]):
                attributes[k] = v
            instance = NBInstance(cl, attributes)
            out.append(instance)
        return out

import sys
def main():
    if len(sys.argv) != 3:
        print("usage: %s training.csv test.csv" % (sys.argv[0],))

    training = load_dataset(sys.argv[1])
    classprobs,attributeprobs = estimate_probabilities(training)

    test = load_dataset(sys.argv[2])
    for instance in test:
        ans = classify(instance, classprobs, attributeprobs)
        correct = (instance.cl == ans)
        print("%s %s" %
          (ans, ("Correct!" if correct else "Wrong!")))

if __name__ == "__main__": main()
