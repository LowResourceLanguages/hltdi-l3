#!/usr/bin/env python3

import sys
import random

import parsetestcases
import naivebayes
import nearestneighbors
import decisiontree
import mostfrequent

from instance import Instance

def load_instances(fn):
    return [Instance(d) for d in parsetestcases.parse(fn)]

def score_difference(scores):
    """Out of all of these scores, what's the distance between the highest
    two?"""
    toptwo = sorted(scores, reverse=True)[:2]
    return abs(toptwo[0] - toptwo[1])

def least_certain(xs, nbc):
    """Out of all the instances listed, which one are we the least certain
    about? Takes a trained naive bayes classifier for estimating
    uncertainties."""
    # We could imagine doing this with two different classifiers, but maybe
    # that doesn't make a lot of sense.
    allscores = [nbc.scores(x) for x in xs]
    differences = [score_difference(scores) for scores in allscores]

    minindex = differences.index(min(differences))
    return xs[minindex]

def run_active_learning(train, xs):
    trainingset = random.sample(xs, len(xs) // 2)
    pool = [x for x in xs if x not in trainingset]

    for it in range(10):
        if pool == []: break
        classifier = train(trainingset)
        nbc = naivebayes.NaiveBayes(trainingset)
        correct = []

        # testset = random.sample(pool, 10)
        testset = pool
        for x in testset:
            if classifier(x) == x.qw:
                correct.append(1)
            else:
                correct.append(0)

        ACTIVESTEPSIZE = 3
        for j in range(ACTIVESTEPSIZE):
            if len(pool) > 0:
                nextpick = least_certain(pool, nbc)
                trainingset.append(nextpick)
                pool.remove(nextpick)

        print("  iteration %2d, accuracy: %d / %d = %0.3f" %
            (it,
             sum(correct), len(correct),
             sum(correct) / len(correct)))

def run_tests(train):
    """Takes a classifier class and runs the leave-one-out testing with it."""

    with open("thecounts", "r") as infile:
        sws = sorted(set([line.strip().split()[0] for line in infile]))
    correct = []
    instances = {}

    for sw in sws:
        instances[sw] = load_instances("testcases/" + sw)
        if len(instances[sw]) >= 50:
            print(sw)
            run_active_learning(train, instances[sw])

def main():
    choices = {
               "KnnWordFeatures":nearestneighbors.KnnWordFeatures,
               "NaiveBayes":naivebayes.NaiveBayes,
               "DecisionTree":decisiontree.DecisionTree,
               }
    if (len(sys.argv) < 2) or sys.argv[1] not in choices:
        print("usage:", sys.argv[0], "<classifier> [text]")
        print("  classifier choices:", sorted(choices.keys()))
        return
    train = choices[sys.argv[1]]
    run_tests(train)

if __name__ == "__main__": main()
