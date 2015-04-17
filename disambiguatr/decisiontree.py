#!/usr/bin/env python3

from nltk.classify import decisiontree

import bagofwords
from learner import Learner

class DecisionTree(Learner):
    def __init__(self, xs):
        sentences = [x.text for x in xs]
        classes = [x.qw for x in xs]

        features = bagofwords.wordfeatures(sentences)
        features = features.union(bagofwords.parsefeatures(xs))
        self.features = features

        self.xs = [bagofwords.bowinstance(x, features) for x in xs]
        training = [(inst.attributes, inst.cl) for inst in self.xs]

        trainer = decisiontree.DecisionTreeClassifier.train

        ## XXX: secret parameter, depth of the decision tree
        self.classifier = trainer(training, depth_cutoff=10, support_cutoff=1)
        # print(self.classifier)

    def __call__(self, x):
        xinst = bagofwords.bowinstance(x, self.features)
        out = self.classifier.classify(xinst.attributes)
        # print([sw for sw in xinst.attributes.keys()
        #           if xinst.attributes[sw] == 1], end=" ")
        # print(out == x.qw)
        return out
