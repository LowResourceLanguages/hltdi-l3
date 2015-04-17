#!/usr/bin/env python3

"""
Pull, out of the AML dictionaries, the Quechua adjectives such that there's
some Spanish word where that word translates to more than one Quechua
adjective.
"""

from collections import defaultdict
import parsexmldict
import spanishutil

def quechua_adjectives(fn):
    """Load the set of Quechua adjectives out of the dictionary file."""
    out = set()
    with open(fn) as infile:
        for line in infile:
            line = line.strip()
            if "adj" in line:
                word = line.split(".")[0]
                out.add(word)
    return out

def check_spanish(fn, qu_adj):
    """Go through the Spanish dictionary, line by line, looking for Spanish
    words that seem to translate to more than one Quechua adjective.
    
    Returns two things: a set of all of the Quechua "target" adjectives and a
    dictionary from Spanish words to lists of Quechua target adjectives.
    """
    quechua_targets = set()
    mapping = defaultdict(lambda: set())
    with open(fn) as infile:
        for line in infile:
            line = line.strip()
            ## replace exclamation points in interjections
            line = line.replace("!", ".")
            line = line.replace("?", ".")
            if "." in line:
                splitted = line.split(".")
                spanishword, pos = splitted[0], splitted[1]
                translationarea = splitted[2]
                translations = translationarea.lower().split(",")
                translations = [tr.strip() for tr in translations]

                adjectives = set([tr for tr in translations if tr in qu_adj])
                if len(adjectives) > 1:
                    if "," in spanishword:
                        spanishword = spanishword.split(",")[0]
                    mapping[spanishword].update(adjectives)
                    for adj in adjectives:
                        quechua_targets.add(adj)
    return quechua_targets, mapping

def spanish_to_quechua():
    """Return a dict from Spanish adjectives to Quechua adjectives, based on
    the parsed dictionaries.""" 
    ### XXX(alexr): duplicated code here, should clean it up.
    es_qu = "dictionaries/DicAMLQuechua-es.txt"
    qu_es = "dictionaries/DicAMLQuechua-qu.txt"
    qu_adj = quechua_adjectives(qu_es)
    targets,mapping = check_spanish(es_qu, qu_adj)
    t2,m2= parsexmldict.runasimi_xml()
    targets.update(t2)
    for k,v in m2.items():
        mapping[k].update(v)
    return mapping

def main():
    es_qu = "dictionaries/DicAMLQuechua-es.txt"
    qu_es = "dictionaries/DicAMLQuechua-qu.txt"

    qu_adj = quechua_adjectives(qu_es)
    targets,mapping = check_spanish(es_qu, qu_adj)

    t2,m2= parsexmldict.runasimi_xml()
    targets.update(t2)
    for k,v in m2.items():
        mapping[k].update(v)

    with open("ambiguouspairs", "w") as outfile:
        for sw in mapping.keys():
            for qw in mapping[sw]:
                outfile.write("{0} {1}\n".format(sw, qw))

    with open("quechuatargets", "w") as outfile:
        for adj in targets:
            outfile.write(adj + "\n")

if __name__ == "__main__": main()
