#!/usr/bin/env python3

"""List out all the words in the Quechua/Spanish dictionary."""

import sys
import l3
from nltkfork.stem.snowball import SpanishStemmer

stemmer = SpanishStemmer()

def loadvocab():
    out = set()
    with open(sys.argv[1]) as infile:
        for line in infile:
            splitted = line.split(".")
            beforeperiod = splitted[0]
            word = beforeperiod.split(",")[0]

            word = word.strip()
            if word:
                ### TODO: make use of AntiMorfo
                analysis = l3.anal_word("es", word, raw=True)
                out.add(stemmer.stem(word.lower()))
        return out

from string import punctuation, whitespace
def main():
    if len(sys.argv) != 3:
        print("usage: enumeratewords.py dictionaryfile sampletext")
        return

    oov = set()
    vocabulary = loadvocab()
    invocabcount = 0
    oovcount = 0

    with open(sys.argv[2]) as infile:
        for line in infile:
            chars = list(line)
            chars = [" " if c in (punctuation + whitespace) else c
                     for c in chars]
            words = ("".join(chars)).lower().split()
            stemmed = [stemmer.stem(word) for word in words]

            for word in stemmed:
                if word in vocabulary:
                    invocabcount += 1
                else:
                    oovcount += 1
                    oov.add(word)
    print("oovcount", oovcount)
    print("invocabcount", invocabcount)
    print("oov", oov)

if __name__ == "__main__": main()
