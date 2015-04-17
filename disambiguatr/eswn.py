#!/usr/bin/env python3

import readline
import copy
from collections import defaultdict

import spanishutil

WN = "wordnet/wn30.src"
SPANISH = "wordnet/senses30.src"

## dictionary from synset ids to synset objects
synsettable = {}

## dictionary from words to lists of synset ids
wordtable = defaultdict(lambda: [])

## dictionary from synset ids to lists of synset ids
hypernymtable = defaultdict(lambda: [])

class Synset(object):
    def __init__(self, synsetid, postag, words):
        self.synsetid = synsetid
        self.postag = postag
        self.words = words
        self.joinedwords = "/".join([synsetid] + words)
    def __str__(self):
        return "<synset {0} {1} {2}>".format(self.synsetid, self.postag,
                                             self.joinedwords)

def loadsynsets():
    """Populate the synsets and words dictionaries."""
    with open(SPANISH, "r", encoding="latin-1") as infile:
        print("ok opened spanish")
        for line in infile:
            line = line.strip()
            if line.startswith("S:"):
                byspaces = line.split(" ")
                bycolons = byspaces[0].split(":")

                synsetid = bycolons[1]
                postag = bycolons[2]
                words = byspaces[1:]

                if synsetid in synsettable:
                    print("warning, duplicate S: entry:", synsetid, words)
                    print("... versus previous:", synsettable[synsetid])

                synsettable[synsetid] = Synset(synsetid, postag, words)

            if line.startswith("W:"):
                byspaces = line.split(" ")
                bycolons = byspaces[0].split(":")
                word = bycolons[1]
                postag = bycolons[2]
                ids = byspaces[1:]
                wordtable[word] += ids

                ## also add the stemmed version; may introduce some ambiguity,
                ## but saves us from having to do morphological analysis on OOV
                ## words in Spanish.
                wordtable[spanishutil.stem(word)] += ids

def loadhypernyms():
    """Returns a dictionary mapping from synsetid to lists of synsetids, where
    the synsetids in the value are all the hypernyms listed for a given
    synset."""
    with open(WN, "r") as infile:
        print("ok opened wn")
        for line in infile:
            byspaces = line.split(" ")

            synset_and_pos = byspaces[0]
            hyperstr = byspaces[1]
            semfile = byspaces[2]
            euronettag = byspaces[3]

            synset = synset_and_pos.split(":")[0]
            hypernym_ids = [] if hyperstr == "-" else hyperstr.split(":")

            if synset in hypernymtable and hypernymtable[synset] is not []:
                # print(hypernyms[synset])
                if synset in synsettable:
                    # print(synsets[synset].words)
                    pass
            hypernymtable[synset] += hypernym_ids

def hypernym_sets(word):
    """Return a list of all the hypernym sets for all paths of hypernymy up
    from each sense of the given word.
    Takes a string and returns a list of sets of synset ids."""

    return [hypernym_set_synset(sense) 
            for sense in wordtable[word]]

def hypernym_set_synset(synset):
    done = set()
    frontier = set([synset])
    while len(frontier) != 0:
        current = frontier.pop() ## we support the axiom of choice.
        hypernyms = hypernymtable[current]
        for hypernym in hypernyms:
            if hypernym not in done:
                frontier.add(hypernym)
        done.add(current)
    return done

def hypernym_paths(word):
    """Return all the paths from this word up to the top of the hypernym
    hierarchy."""
    out = []
    synsets = wordtable[word]
    for sense in synsets:
        out += hypernym_paths_synset(sense)
    return out

def hypernym_paths_synset(synset, seen=set()):
    """Returns a list of lists of the paths from this synset to the most
    abstract synset above this one."""
    paths = []
    hypernyms = hypernymtable[synset]
    if len(hypernyms) == 0:
        # at the top!
        return [[synset]]
    for hypernym in hypernyms:
        if hypernym in seen:
            continue
        seen.add(hypernym)
        further = hypernym_paths_synset(hypernym, copy.deepcopy(seen))
        for path in further:
            paths.append( [synset] + path )
    return paths

def hypernym_bigset(word):
    """Actually only get the first three synsets."""
    paths = hypernym_paths(word)
    out = set()
    for p in paths:
        out.update(p[:3])
    # print(out)
    return out

def repl():
    try:
        while True:
            print("word? ", end="")
            word = input().strip()
            example_with_sets(word)
            example_with_paths(word)
    finally:
        return

def example_with_sets(word):
    sets = hypernym_sets(word)
    print("\n** {0} has {1} senses. **".format(word, len(wordtable[word])))
    for i,hypernymset in enumerate(sets):
        out = [synsettable[sense].joinedwords
               if sense in synsettable else sense
               for sense in hypernymset]
        print("{0}".format(out))

def example_with_paths(word):
    paths = hypernym_paths(word)
    print("\n** {0} has {1} paths up. **".format(word, len(paths)))
    for i,path in enumerate(paths):

        out = [synsettable[sense].joinedwords
               if sense in synsettable else sense
               for sense in path]
        print("{0}".format(out))

print("eswn: loading Spanish wordnet...")
loadsynsets()
loadhypernyms()

def main():
    repl()
    print()

if __name__ == "__main__": main()
