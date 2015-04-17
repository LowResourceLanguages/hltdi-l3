#!/usr/bin/env python3

"""Get all the useful pairs of adjectives with nouns out of the elicitation
corpora."""

import os, glob

import extract

quechuapos = set()
def extractfrompair(srcsent, tgtsent, aligned):
    spanishwords = srcsent.strip().split()
    quechuawords = tgtsent.strip().split()
    ## find all the cases where we see a Quechua word that's an adjective,
    ## followed by a noun.
    
    adjectives = []
    for qw in quechuawords:
        qw = qw.replace("+","")
        answers = extract.quechuaMA(qw)
        for answer in answers:
            if answer is not None and answer[1] is not None:
                try:
                    quechuapos.add(answer[1]['pos'])
                    if answer[1]['pos'] == 'adj':
                        adjectives.append(qw)
                except:
                    continue
    if adjectives:
        print("srcsent:", srcsent)
        print("tgtsent:", tgtsent)
        print("aligned:", aligned)
        print("adjectives:", adjectives)

def extract_fn(fn):
    srcsent,tgtsent,aligned = None,None,None
    with open(fn, encoding="latin-1") as infile:
        for line in infile:
            line = line.strip()
            if line == "newpair":
                srcsent,tgtsent,aligned = None,None,None

            if line.startswith("srcsent:"):
                srcsent = line.split(":")[1]
            if line.startswith("tgtsent:"):
                tgtsent = line.split(":")[1]
            if line.startswith("aligned:"):
                aligned = line.split(":")[1]

            if srcsent and tgtsent and aligned:
                extractfrompair(srcsent, tgtsent, aligned)
                # extractfrompair_es(srcsent, tgtsent, aligned)

def main():
    elicitation = os.path.expanduser("~/corpora/Quechua/Elicitation/CorpusDone")
    fns = glob.glob(elicitation + "/[FS]C*.txt")

    extract.load_spanish_adjectives()

    for fn in fns:
        print("**** {0} ****".format(fn))
        extract_fn(fn)
    print(quechuapos)

if __name__ == "__main__": main()
