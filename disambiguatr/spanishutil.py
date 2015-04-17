#!/usr/bin/env python3

"""Routines for dealing with Spanish words."""

import string
from nltk.stem.snowball import SpanishStemmer

vowels = "aeiouáéíóú"
spanishpunct = "\xAB\xBB\xBF\xA1"

def pluralize(word):
    """Try to figure out the plural for an adjective."""
    if word[-1] in vowels:
        return word + "s"
    if word[-1] == 'z':
        return word[:-1] + "ces"
    else:
        return word + "es"

def justletters(s):
    """Given a string that might contain puncuation or accents, strip it
    out."""
    allpunct = spanishpunct + string.punctuation
    spaces = (" " * len(allpunct))

    trans1 = str.maketrans("áéíóúñ", "aeioun")
    trans2 = str.maketrans(allpunct, spaces)

    noaccents = s.translate(trans1)
    return noaccents.translate(trans2)

def remove_stopwords(words):
    return [w for w in words if w not in stopwords]

def stem_words(words):
    return [stem(w) for w in words]

def normalize_split(text):
    """Given some text, take out punctuation and diacritics, then split."""
    splitted = justletters(text).lower().split()
    return splitted

def wordversions(word):
    """Given a string of the form verdadero,–ra, return
    ["verdadero", "verdadera", "verdaderos", "verdaderas"].
    Assumes the rule, which seems to be good for Spanish adjectives, that if
    the input string has a comma, you make the feminine by:
    - if the word ends with o, remove it and add an a.
    - otherwise, just add an a.
    If there's no comma, the word doesn't inflect for gender."""

    if word.endswith("os"):
        # for "algunos", "algunas"
        return [word, word[:-2] + "as"]

    if word[-1] in "rle":
        return [word, pluralize(word)]

    if word.endswith('a'):
        feminine = word
        masculine = feminine[:-1] + "o"
    else:
        masculine = word
        feminine = (masculine[:-1] + "a" if masculine.endswith("o")
                                         else masculine + "a")
    return [masculine, pluralize(masculine),
           feminine, pluralize(feminine)]

thestemmer = SpanishStemmer()
def stem(word):
    return thestemmer.stem(word)

stopwords = None
with open("dictionaries/stopwords_es") as infile:
    stopwords = set()
    for line in infile:
        stopwords.add(justletters(line.strip()))
        stopwords.add(line.strip())

def main():
    """simple main for seeing how well we do. Does this produce
    sensible-looking inflections?"""

    with open("ambiguouspairs", "r") as infile:
        for line in infile:
            line = line.strip()
            sw = line.split(" ")[0]
            print(wordversions(sw))

if __name__ == "__main__": main()
