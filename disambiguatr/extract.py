#!/usr/bin/env python3

"""
Common routines for pulling useful examples of Quechua adjectives the
generation of which requires lexical choice.

Used by extractbibles and extractelicitation at least!
"""

import yaml
import l3

es_adj = set()
def load_spanish_adjectives():
    spanish_adj_fn = "../l3xdg/languages/es/es_adj.yaml"
    with open(spanish_adj_fn) as infile:
        adjs = yaml.load(infile)
        for entry in adjs:
            if "word" in entry:
                es_adj.add(entry["word"])

quechua_cache = {}
def quechuaMA(word):
    """Caching wrapper around the l3 Quechua morphological analyzer."""
    if word not in quechua_cache:
        quechua_cache[word] = l3.anal_word("qu", word, raw=True)
    return quechua_cache[word]

def get_pos(word):
    """Given a word in Spanish, return its POS tag."""
    pass
    ## try looking up the word in a dictionary.
    ## which dictionaries of Spanish do we have?
    ## runasimi, spanish wordnet, dicAML...

    ## how do we deal with morphology in Spanish? What if we're looking for
    ## "alta", but only "alto" is in the dictionary? Do stemming? 
    ## can morphological analysis with AntiMorfo help?

    ## failing that, return "OOV".

