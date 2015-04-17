#!/usr/bin/env python3

import math

def infogain(xs, feat):
    ## Entropy before knowing the feature, minus entropy after knowing it.
    return entropy([x.cl for x in xs]) - conditional_entropy(xs,feat)

def conditional_entropy(xs, feat):
    """Instances are things with .attributes and .cl members, where .cl is
    their class, and .attributes is a dictionary from features to values.
    Return the conditional entropy of the class, given the attribute."""

    ## for every value of the feature...
    ## sum up (probability of that value) * (entropy of class in instances
    ##                                         with that feature value)
    featvalues = set(x.attributes[feat] for x in xs)

    total = 0
    for val in featvalues:
        ## prob of that value
        count = [x.attributes[feat] for x in xs].count(val)
        prob = count / len(xs)

        ## entropy over the class, for this feat/value
        classes_for_this_value = [x.cl for x in xs
                                       if x.attributes[feat] == val]
        total += prob * entropy(classes_for_this_value)
    return total

def entropy(xs):
    """Given a list of items, what's the entropy on the random variable of
    picking one of the values?"""
    total = 0
    values = set(xs)
    for val in values:
        prob = xs.count(val) / len(xs)
        total += prob * math.log(prob, 2)
    return -total

## The Gladiator example from Andrew Moore, just to test this out.
## http://www.autonlab.org/tutorials/infogain.html
class Student:
    def __init__(self, major, gladiator):
        self.cl = gladiator
        self.attributes = {}
        self.attributes["major"] = major

def main():
    print(entropy(range(2)))
    print(entropy([0,0,1,1,2,2,3,3]))
    print(entropy([0,0,1,1,2,2]))

    students = [
        Student("Math", "Yes"),
        Student("History", "No"),
        Student("CS", "Yes"),
        Student("Misc", "No"), ## changed major from Math
        Student("Misc", "No"), ## changed major from Math
        Student("CS", "Yes"),
        Student("History", "No"),
        Student("Math", "Yes"),
    ]
    print(conditional_entropy(students, "major"))
    print(infogain(students, "major"))

if __name__ == "__main__": main()
