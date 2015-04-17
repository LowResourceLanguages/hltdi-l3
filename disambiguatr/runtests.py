#!/usr/bin/env python3

import sys
import math

import parsetestcases
from instance import Instance

def load_instances(fn):
    return [Instance(d) for d in parsetestcases.parse(fn)]

## for reporting the "pick one uniformly" baseline.
totalchoices = 0

def run_tests(train):
    """Takes a classifier class and runs the leave-one-out testing with it."""

    ncorrect, ntrials, ndisagree, ndisagree_and_correct = 0,0,0,0

    with open("thecounts", "r") as infile:
        sws = sorted(set([line.strip().split()[0] for line in infile]))
    correct = []
    instances = {}
    for sw in sws:
        print(sw)
        instances[sw] = load_instances("testcases/" + sw)

        nc,nt,nd,ndac = nfold(10, instances[sw], train)
        ncorrect += nc
        ntrials += nt
        ndisagree += nd
        ndisagree_and_correct += ndac

    print("Overall!!")
    print_metrics(ncorrect, ntrials, ndisagree, ndisagree_and_correct)
    print("  if picking uniformly: %0.3f" % (ntrials / totalchoices ,))

def nfold(n, xs, train):
    global totalchoices 
    """Do n-fold cross validation."""
    correct = []

    totalchoices += len(xs) * len(set([x.cl for x in xs]))
    print(totalchoices)

    size = len(xs) // n
    if size == 0:
        n = len(xs)
        size = 1
    n = math.ceil(len(xs) / size)

    ndisagree = 0
    ncorrect = 0
    ndisagree_and_correct = 0
    ntrials = 0

    for it in range(n):
        indices = range(len(xs))
        testindices = range(it * size, (it+1) * size)
        trainonthese = [xs[index] for index in indices
                                  if index not in testindices]
        testonthese  = [xs[index] for index in indices
                                  if index in testindices]
        classifier = train(trainonthese)
        baseline_classifier = MostFrequentBaseline(trainonthese)

        for x in testonthese:
            ntrials += 1
            predicted = classifier(x)
            if predicted == x.qw:
                ncorrect += 1
            if predicted != baseline_classifier(x):
                ndisagree += 1
                if predicted == x.qw:
                    ndisagree_and_correct += 1
    assert ntrials == len(xs)
    print_metrics(ncorrect, ntrials, ndisagree, ndisagree_and_correct)
    return ncorrect, ntrials, ndisagree, ndisagree_and_correct

def print_metrics(nc, nt, nd, ndac):
    """Print some helpful statistics."""
    print("  accuracy: %d / %d = %0.3f" % (nc, nt, nc / nt))
    print("  disagreed: %d / %d = %0.3f" % (nd, nt, nd / nt))
    if nd > 0:
        print("  disagree accuracy: %d / %d = %0.3f" % (ndac, nd, ndac / nd))
    else:
        print("  disagree accuracy: 0 / 0 = 0")

from learner import Learner
from mostfrequent import MostFrequentBaseline
from mostfrequent import MostFrequentOverText
from nearestneighbors import KnnWithWordnet
from nearestneighbors import KnnWordFeatures
from naivebayes import NaiveBayes
from decisiontree import DecisionTree
from lesk import Lesk

environment = dir()
def main():
    envpairs = [(name, eval(name)) for name in environment]
    choices = dict([(name, thing) for (name,thing) in envpairs
                                  if (isinstance(thing, type) and
                                      issubclass(thing, Learner))])
    if (len(sys.argv) < 2) or sys.argv[1] not in choices:
        print("usage:", sys.argv[0], "<classifier> [text]")
        print("  classifier choices:", sorted(choices.keys()))
        return
    train = choices[sys.argv[1]]
    train.Initialize()

    run_tests(train)

if __name__ == "__main__": main()
